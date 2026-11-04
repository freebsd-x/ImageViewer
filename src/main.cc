// ImageViewer.xapp — Image viewer for FreeBSD-X
//
// Features:
//   • Pinch-to-zoom (GestureDetectorWidget) and pan with bounds clamping
//   • Keyboard: Left/Right arrows = prev/next, +/- = zoom, Space = slideshow toggle
//   • Slideshow mode: auto-advance on configurable interval (default 4 s)
//   • Folder browsing: a file passed at launch brings its folder's images with it;
//     one picked later is shown alone, since the sandbox gets only that file
//   • Collapsible EXIF/metadata sidebar (Make, Model, DateTime, dimensions, file size)
//   • EXIF parsed inline from JPEG APP1 and PNG IHDR/tEXt chunks — no extra deps
//   • MIME handler for image/jpeg, image/png, image/gif, image/webp, image/*
//   • Opens via argv[1], the Open button, or a drop (which asks through the picker)
//   • Decodes through FFmpeg from a descriptor: no path is opened after start-up

#include "xkit/widget.h"
#include "xkit/application.h"
#include "xkit/xbus_client.h"
#include "xkit/file_dialog.h"
#include "xkit/media_file.h"
#include "xrender/svg_engine.h"
#include "shared/protocol.h"
#include <memory>
#include <string>
#include <vector>
#include <cstring>
#include <cstdlib>
#include <cstdint>
#include <cstdio>
#include <cmath>
#include <algorithm>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <thread>
#include <atomic>
#include <mutex>
#include <chrono>
#include <fcntl.h>
#include <unistd.h>
#include <sys/capsicum.h>

namespace fs = std::filesystem;
using namespace fbx::xkit;
using namespace fbx::shared;

// ── Image extensions ──────────────────────────────────────────────────────────

static bool isImageFile(const std::string& p) {
    static const char* exts[] = {
        ".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp",
        ".tiff", ".tif", ".avif", ".svg", nullptr
    };
    std::string lower = p;
    std::transform(lower.begin(), lower.end(), lower.begin(), ::tolower);
    for (int i = 0; exts[i]; ++i)
        if (lower.ends_with(exts[i])) return true;
    return false;
}

static std::string basename(const std::string& path) {
    auto p = path.rfind('/');
    return (p == std::string::npos) ? path : path.substr(p + 1);
}

// ── File size helper ──────────────────────────────────────────────────────────

static std::string fileSizeStr(size_t bytes) {
    double sz = static_cast<double>(bytes);
    if (sz < 1024)        return std::to_string(static_cast<int>(sz)) + " B";
    if (sz < 1024*1024)   return std::to_string(static_cast<int>(sz/1024)) + " KB";
    char buf[32];
    std::snprintf(buf, sizeof(buf), "%.1f MB", sz / (1024.0*1024.0));
    return buf;
}

// ── Inline EXIF / metadata parser ────────────────────────────────────────────

struct ExifInfo {
    uint32_t    width{0};
    uint32_t    height{0};
    std::string make;
    std::string model;
    std::string date_time;
    std::string exposure_time;
    std::string f_number;
    std::string iso;
};

namespace {

// Read u16/u32 respecting byte order (ii=little-endian, mm=big-endian)
static uint16_t readU16(const uint8_t* p, bool le) {
    return le ? (uint16_t)(p[0] | (p[1] << 8))
              : (uint16_t)((p[0] << 8) | p[1]);
}
static uint32_t readU32(const uint8_t* p, bool le) {
    return le ? ((uint32_t)p[0] | ((uint32_t)p[1]<<8) |
                 ((uint32_t)p[2]<<16) | ((uint32_t)p[3]<<24))
              : ((uint32_t)p[0]<<24 | (uint32_t)p[1]<<16 |
                 (uint32_t)p[2]<<8  | (uint32_t)p[3]);
}

// Read a null-terminated ASCII string from TIFF IFD value (type=2)
static std::string tiffString(const uint8_t* base, uint32_t count,
                               uint32_t value_offset_raw, bool le,
                               size_t data_len) {
    if (count <= 4) {
        // value fits inline in the 4-byte value field
        std::string s;
        s.assign(reinterpret_cast<const char*>(&value_offset_raw),
                 std::min((size_t)(count - 1), (size_t)4));
        return s;
    }
    uint32_t off = le
        ? value_offset_raw
        : __builtin_bswap32(value_offset_raw);
    if (off + count > data_len) return {};
    std::string s(reinterpret_cast<const char*>(base + off),
                  count > 1 ? count - 1 : 0);
    return s;
}

// Parse a TIFF IFD and fill ExifInfo fields; returns ExifIFD sub-offset (or 0)
static uint32_t parseTiffIfd(const uint8_t* base, uint32_t ifd_off,
                              bool le, size_t len, ExifInfo& out) {
    if (ifd_off + 2 > len) return 0;
    uint16_t nentries = readU16(base + ifd_off, le);
    ifd_off += 2;
    uint32_t exif_ifd_off = 0;
    for (uint16_t i = 0; i < nentries; ++i) {
        uint32_t entry_off = ifd_off + i * 12;
        if (entry_off + 12 > len) break;
        uint16_t tag   = readU16(base + entry_off, le);
        uint16_t type  = readU16(base + entry_off + 2, le);
        uint32_t count = readU32(base + entry_off + 4, le);
        uint32_t raw_val;
        std::memcpy(&raw_val, base + entry_off + 8, 4);
        (void)type;

        auto asStr = [&]() {
            return tiffString(base, count, raw_val, le, len);
        };
        auto asU32 = [&]() -> uint32_t {
            return le ? raw_val : __builtin_bswap32(raw_val);
        };
        auto asRational = [&]() -> std::string {
            uint32_t off = asU32();
            if (off + 8 > len) return {};
            uint32_t num = readU32(base + off, le);
            uint32_t den = readU32(base + off + 4, le);
            if (den == 0) return {};
            char buf[32];
            if (num < den)
                std::snprintf(buf, sizeof(buf), "1/%u", den / num);
            else
                std::snprintf(buf, sizeof(buf), "%.1f", (double)num / den);
            return buf;
        };

        switch (tag) {
        case 0x010F: out.make      = asStr();      break; // Make
        case 0x0110: out.model     = asStr();      break; // Model
        case 0x0132: out.date_time = asStr();      break; // DateTime
        case 0x0100: out.width     = asU32();      break; // ImageWidth
        case 0x0101: out.height    = asU32();      break; // ImageLength
        case 0x8769: exif_ifd_off  = asU32();      break; // ExifIFD pointer
        case 0x829A: out.exposure_time = asRational(); break; // ExposureTime
        case 0x829D: out.f_number      = asRational(); break; // FNumber
        case 0x8827: {                                      // ISOSpeedRatings
            uint32_t off2 = asU32();
            if (count >= 1 && off2 + 2 <= len)
                out.iso = std::to_string(readU16(base + off2, le));
            break;
        }
        default: break;
        }
    }
    return exif_ifd_off;
}

// Parse JPEG file: find APP1 for EXIF, SOF0/SOF2 for dimensions
static ExifInfo parseJpeg(const std::string& bytes) {
    ExifInfo info;
    const auto* data = reinterpret_cast<const uint8_t*>(bytes.data());
    size_t len = bytes.size();
    if (len < 4 || data[0] != 0xFF || data[1] != 0xD8) return info;

    size_t pos = 2;
    while (pos + 4 <= len) {
        if (data[pos] != 0xFF) break;
        uint8_t  marker = data[pos + 1];
        uint16_t seg_len = (uint16_t)((data[pos+2] << 8) | data[pos+3]);
        if (seg_len < 2) break;

        // SOF0, SOF1, SOF2 — image dimensions
        if ((marker == 0xC0 || marker == 0xC1 || marker == 0xC2) &&
            pos + 11 <= len) {
            info.height = (data[pos+5] << 8) | data[pos+6];
            info.width  = (data[pos+7] << 8) | data[pos+8];
        }

        // APP1 — EXIF
        if (marker == 0xE1 && seg_len > 8 &&
            pos + seg_len <= len &&
            std::memcmp(&data[pos+4], "Exif\0\0", 6) == 0) {
            const uint8_t* tiff = &data[pos + 10];
            size_t tiff_len = seg_len - 8;
            bool le = (tiff[0] == 'I' && tiff[1] == 'I');
            uint32_t ifd0_off = readU32(tiff + 4, le);
            uint32_t exif_off = parseTiffIfd(tiff, ifd0_off, le, tiff_len, info);
            if (exif_off)
                parseTiffIfd(tiff, exif_off, le, tiff_len, info);
        }

        if (marker == 0xD9 || marker == 0xDA) break; // EOI / SOS
        pos += 2 + seg_len;
    }
    return info;
}

// Parse PNG file: IHDR for dimensions, tEXt/iTXt for metadata
static ExifInfo parsePng(const std::string& bytes) {
    ExifInfo info;
    std::istringstream f(bytes);
    uint8_t sig[8];
    f.read(reinterpret_cast<char*>(sig), 8);
    if (f.gcount() < 8) return info;
    static const uint8_t kPngSig[8] = {137,80,78,71,13,10,26,10};
    if (std::memcmp(sig, kPngSig, 8) != 0) return info;

    while (f) {
        uint8_t hdr[8];
        f.read(reinterpret_cast<char*>(hdr), 8);
        if (f.gcount() < 8) break;
        uint32_t chunk_len = ((uint32_t)hdr[0]<<24)|((uint32_t)hdr[1]<<16)|
                             ((uint32_t)hdr[2]<<8) | hdr[3];
        char type[5]{}; std::memcpy(type, hdr+4, 4);
        if (chunk_len > bytes.size()) break;   // a damaged length, not a real chunk
        std::vector<uint8_t> chunk(chunk_len);
        f.read(reinterpret_cast<char*>(chunk.data()), chunk_len);
        f.ignore(4); // CRC

        if (std::strcmp(type, "IHDR") == 0 && chunk_len >= 8) {
            info.width  = readU32(chunk.data(),   false);
            info.height = readU32(chunk.data()+4, false);
        } else if (std::strcmp(type, "tEXt") == 0) {
            // "keyword\0text"
            auto nul = std::find(chunk.begin(), chunk.end(), 0);
            if (nul != chunk.end()) {
                std::string key(chunk.begin(), nul);
                std::string val(nul + 1, chunk.end());
                if (key == "Author")   info.make  = val;
                if (key == "Software") info.model = val;
                if (key == "Creation Time") info.date_time = val;
            }
        } else if (std::strcmp(type, "IEND") == 0) {
            break;
        }
    }
    return info;
}

static ExifInfo parseExif(const std::string& path, const std::string& bytes) {
    std::string lower = path;
    std::transform(lower.begin(), lower.end(), lower.begin(), ::tolower);
    if (lower.ends_with(".jpg") || lower.ends_with(".jpeg"))
        return parseJpeg(bytes);
    if (lower.ends_with(".png"))
        return parsePng(bytes);
    ExifInfo info;
    return info; // unsupported format — caller shows just filename
}

} // anonymous namespace

// ── App ───────────────────────────────────────────────────────────────────────

int main(int argc, char** argv) {
    // ── Viewer state ──────────────────────────────────────────────────────────
    static std::vector<std::string> files;    // directory image list
    static int   file_idx      = 0;
    static float scale_        = 1.0f;
    static float pan_x_        = 0.0f;
    static float pan_y_        = 0.0f;
    static bool  info_open_    = false;
    static bool  slideshow_    = false;
    static std::atomic<bool> ss_running_{false};

    // Widgets updated across functions
    static std::shared_ptr<FlexColumn> img_area;    // image + gesture
    static std::shared_ptr<FlexColumn> info_col;    // EXIF sidebar
    static std::shared_ptr<TextWidget> filename_lbl;
    static std::shared_ptr<TextWidget> counter_lbl;
    static std::shared_ptr<TextWidget> zoom_lbl;
    static std::shared_ptr<TextWidget> slideshow_lbl;
    static std::shared_ptr<FlexRow>    body_row;

    // Forward declarations
    static std::function<void(int)>   open_index;
    static std::function<void()>      rebuild_info;
    static std::function<void()>      start_slideshow;
    static std::function<void()>      stop_slideshow;

    // ── Where the images come from ────────────────────────────────────────────
    // The folder of a file given at launch (opened before the sandbox, and
    // limited to reading what's in it), or the one file picked afterwards.
    static int dir_fd = -1;
    static fbx::xserver::UniqueFd picked_fd;

    static std::string loaded_path;     // what the fields below hold
    static std::string loaded_bytes;
    static std::vector<uint8_t> loaded_pixels;
    static uint32_t loaded_w = 0, loaded_h = 0;
    static std::string load_error;

    static auto load_image = [](const std::string& path) {
        loaded_path = path;
        loaded_pixels.clear();
        loaded_bytes.clear();
        load_error.clear();

        fbx::xserver::UniqueFd sibling;
        int fd = picked_fd.get();
        if (fd < 0) {
            sibling = fbx::xserver::UniqueFd(::openat(dir_fd, basename(path).c_str(), O_RDONLY | O_CLOEXEC));
            fd = sibling.get();
        }
        if (fd < 0) { load_error = std::strerror(errno); return; }
        if (!readAllFd(fd, loaded_bytes)) { load_error = "couldn't read the file"; return; }

        std::string lower = path;
        std::transform(lower.begin(), lower.end(), lower.begin(), ::tolower);
        if (lower.ends_with(".svg")) {
            auto svg = fbx::xrender::SvgEngine::decode(loaded_bytes, 1024, 768);
            if (!svg) { load_error = "the SVG couldn't be drawn"; return; }
            loaded_pixels = std::move(svg->pixels_);
            loaded_w = svg->width_;
            loaded_h = svg->height_;
            return;
        }
        (void)decodeImageFd(fd, basename(path), loaded_pixels, loaded_w, loaded_h, load_error);
    };

    // Show the file `index` of `found`, giving up what was shown before.
    static auto show_files = [](std::vector<std::string> found, const std::string& current) {
        stop_slideshow();
        files = std::move(found);
        file_idx = 0;
        for (int i = 0; i < (int)files.size(); ++i)
            if (files[i] == current) { file_idx = i; break; }
        loaded_path.clear();
        open_index(file_idx);
        XApplication::setTitle(std::string("Image Viewer — ") + basename(current));
    };

    // Past start-up the sandbox opens no paths: the user picks, in the shell.
    static auto pick_image = [](const std::string& folder) {
        auto* bus = XApplication::getBus();
        if (!bus) return;
        XFileDialog::pickToOpen(*bus, "Open Image", folder, [](XFileDialog::Picked p) {
            if (p.cancelled) return;
            if (!p.fd) {
                if (filename_lbl) filename_lbl->setText("Couldn't open that file: " + p.error);
                return;
            }
            picked_fd = std::move(p.fd);
            show_files({p.path}, p.path);
        });
    };

    // ── Rebuild EXIF sidebar ──────────────────────────────────────────────────
    rebuild_info = []() {
        if (!info_col) return;
        info_col->clearChildren();

        auto row = [](const std::string& k, const std::string& v)
            -> std::shared_ptr<Widget> {
            auto kw = std::make_shared<TextWidget>(k + ":", 11.0f);
            kw->setColor(Color{0.6f, 0.6f, 0.65f, 1.0f});
            auto vw = std::make_shared<TextWidget>(v.empty() ? "—" : v, 11.0f);
            vw->setColor(Color{0.9f, 0.9f, 0.9f, 1.0f});
            vw->setFlexGrow(1.0f);
            auto r = std::make_shared<FlexRow>(
                std::vector<std::shared_ptr<Widget>>{kw, std::make_shared<Spacer>(6,0), vw});
            r->setCrossAxisAlignment(CrossAxisAlignment::Start);
            r->setPadding(2.0f);
            return r;
        };

        if (files.empty()) return;
        const std::string& path = files[file_idx];
        ExifInfo ex = parseExif(path, loaded_bytes);

        auto hdr = std::make_shared<TextWidget>("Image Info", 13.0f);
        hdr->setColor(Color{0.9f, 0.9f, 0.9f, 1.0f});
        info_col->addChild([&]{ auto c = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{hdr}); c->setPadding(4.0f); return c; }());
        info_col->addChild(std::make_shared<DividerWidget>());

        info_col->addChild(row("File",  basename(path)));
        info_col->addChild(row("Size",  fileSizeStr(loaded_bytes.size())));
        if (ex.width && ex.height) {
            info_col->addChild(row("Dims",
                std::to_string(ex.width) + " × " + std::to_string(ex.height)));
        }
        if (!ex.make.empty())          info_col->addChild(row("Make",  ex.make));
        if (!ex.model.empty())         info_col->addChild(row("Model", ex.model));
        if (!ex.date_time.empty())     info_col->addChild(row("Date",  ex.date_time));
        if (!ex.exposure_time.empty()) info_col->addChild(row("Exp",   ex.exposure_time + " s"));
        if (!ex.f_number.empty())      info_col->addChild(row("f/",    ex.f_number));
        if (!ex.iso.empty())           info_col->addChild(row("ISO",   ex.iso));
    };

    // ── Open image at index ───────────────────────────────────────────────────
    open_index = [](int idx) {
        if (files.empty()) return;
        idx = ((idx % (int)files.size()) + (int)files.size()) % (int)files.size();
        file_idx = idx;

        // Reset zoom & pan
        scale_ = 1.0f;
        pan_x_ = 0.0f;
        pan_y_ = 0.0f;

        const std::string path = files[file_idx];
        // Zooming and panning come back here; only a different file is read.
        if (path != loaded_path) load_image(path);

        if (filename_lbl) filename_lbl->setText(basename(path));
        if (counter_lbl)
            counter_lbl->setText(std::to_string(file_idx + 1) + " / " +
                                 std::to_string(files.size()));
        if (zoom_lbl) zoom_lbl->setText("100%");

        // Rebuild image display
        if (img_area) {
            img_area->clearChildren();
            if (loaded_pixels.empty()) {
                auto msg = std::make_shared<TextWidget>(
                    "Can't show " + basename(path) + ": " + load_error, 14.0f);
                msg->setColor(Color{0.95f, 0.60f, 0.55f, 1.0f});
                img_area->addChild(msg);
                if (info_open_) rebuild_info();
                return;
            }

            // Display image at 800×600 base, scaled
            constexpr float kBaseW = 800.0f, kBaseH = 600.0f;
            float disp_w = kBaseW * scale_;
            float disp_h = kBaseH * scale_;

            auto img = std::make_shared<ImageWidget>(loaded_pixels, loaded_w, loaded_h);
            img->setFitMode(ImageFitMode::Contain);
            img->setFixedSize(disp_w, disp_h);
            img->setMargin(pan_y_ < 0 ? -pan_y_ : 0.0f,
                           pan_x_ < 0 ? -pan_x_ : 0.0f,
                           pan_y_ > 0 ? pan_y_  : 0.0f,
                           pan_x_ > 0 ? pan_x_  : 0.0f);

            auto gesture = std::make_shared<GestureDetectorWidget>(
                img,
                // onTap — do nothing (could toggle info)
                nullptr,
                // onPan
                [](float dx, float dy) {
                    constexpr float kMaxPan = 400.0f;
                    pan_x_ = std::clamp(pan_x_ + dx, -kMaxPan, kMaxPan);
                    pan_y_ = std::clamp(pan_y_ + dy, -kMaxPan, kMaxPan);
                    // Rebuild view with new pan
                    open_index(file_idx);
                },
                // onPinch
                [](float ds, float /*cx*/, float /*cy*/) {
                    scale_ = std::clamp(scale_ * ds, 0.1f, 8.0f);
                    if (zoom_lbl)
                        zoom_lbl->setText(std::to_string(
                            static_cast<int>(scale_ * 100)) + "%");
                    open_index(file_idx);
                });
            gesture->setFlexGrow(1.0f);

            img_area->addChild(gesture);
        }

        if (info_open_) rebuild_info();
    };

    // ── Slideshow ─────────────────────────────────────────────────────────────
    start_slideshow = []() {
        if (ss_running_.exchange(true)) return;
        slideshow_ = true;
        if (slideshow_lbl) slideshow_lbl->setText("⏸ Slide");
        std::thread([]() {
            while (ss_running_.load()) {
                std::this_thread::sleep_for(std::chrono::seconds(4));
                if (ss_running_.load())
                    open_index(file_idx + 1);
            }
        }).detach();
    };

    stop_slideshow = []() {
        ss_running_.store(false);
        slideshow_ = false;
        if (slideshow_lbl) slideshow_lbl->setText("▶ Slide");
    };

    // ── Toolbar ───────────────────────────────────────────────────────────────
    auto prev_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>(" ← ", 14.0f),
        []() { stop_slideshow(); open_index(file_idx - 1); });
    prev_btn->setBackgroundColor(Color{0.18f, 0.18f, 0.20f, 1.0f});

    auto next_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>(" → ", 14.0f),
        []() { stop_slideshow(); open_index(file_idx + 1); });
    next_btn->setBackgroundColor(Color{0.18f, 0.18f, 0.20f, 1.0f});

    slideshow_lbl = std::make_shared<TextWidget>("▶ Slide", 12.0f);
    auto ss_btn = std::make_shared<ButtonWidget>(slideshow_lbl, []() {
        if (slideshow_) stop_slideshow();
        else            start_slideshow();
    });
    ss_btn->setBackgroundColor(Color{0.18f, 0.18f, 0.20f, 1.0f});

    zoom_lbl = std::make_shared<TextWidget>("100%", 12.0f);
    zoom_lbl->setColor(Color{0.75f, 0.75f, 0.75f, 1.0f});

    auto zoom_in_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>(" + ", 14.0f),
        []() {
            scale_ = std::clamp(scale_ * 1.25f, 0.1f, 8.0f);
            if (zoom_lbl)
                zoom_lbl->setText(std::to_string(
                    static_cast<int>(scale_ * 100)) + "%");
            open_index(file_idx);
        });
    zoom_in_btn->setBackgroundColor(Color{0.18f, 0.18f, 0.20f, 1.0f});

    auto zoom_out_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>(" − ", 14.0f),
        []() {
            scale_ = std::clamp(scale_ / 1.25f, 0.1f, 8.0f);
            if (zoom_lbl)
                zoom_lbl->setText(std::to_string(
                    static_cast<int>(scale_ * 100)) + "%");
            open_index(file_idx);
        });
    zoom_out_btn->setBackgroundColor(Color{0.18f, 0.18f, 0.20f, 1.0f});

    auto zoom_reset_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>(" 1:1 ", 12.0f),
        []() {
            scale_ = 1.0f; pan_x_ = 0.0f; pan_y_ = 0.0f;
            if (zoom_lbl) zoom_lbl->setText("100%");
            open_index(file_idx);
        });
    zoom_reset_btn->setBackgroundColor(Color{0.18f, 0.18f, 0.20f, 1.0f});

    filename_lbl = std::make_shared<TextWidget>("No image", 13.0f);
    filename_lbl->setColor(Color{0.9f, 0.9f, 0.9f, 1.0f});
    filename_lbl->setFlexGrow(1.0f);

    counter_lbl = std::make_shared<TextWidget>("", 12.0f);
    counter_lbl->setColor(Color{0.6f, 0.6f, 0.6f, 1.0f});

    // Info panel toggle button
    auto info_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>(" ℹ ", 14.0f),
        []() {
            info_open_ = !info_open_;
            if (info_col)
                info_col->setFixedSize(info_open_ ? 200.0f : 0.0f, 0.0f);
            if (info_open_) rebuild_info();
        });
    info_btn->setBackgroundColor(Color{0.18f, 0.18f, 0.20f, 1.0f});

    auto open_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>(" Open… ", 12.0f), []() { pick_image(""); });
    open_btn->setBackgroundColor(Color{0.18f, 0.18f, 0.20f, 1.0f});

    auto toolbar = std::make_shared<FlexRow>(std::vector<std::shared_ptr<Widget>>{
        open_btn,
        std::make_shared<Spacer>(8, 0),
        prev_btn,
        std::make_shared<Spacer>(4, 0),
        next_btn,
        std::make_shared<Spacer>(8, 0),
        ss_btn,
        std::make_shared<Spacer>(12, 0),
        filename_lbl,
        std::make_shared<Spacer>(8, 0),
        counter_lbl,
        std::make_shared<Spacer>(12, 0),
        zoom_out_btn,
        std::make_shared<Spacer>(4, 0),
        zoom_lbl,
        std::make_shared<Spacer>(4, 0),
        zoom_in_btn,
        std::make_shared<Spacer>(4, 0),
        zoom_reset_btn,
        std::make_shared<Spacer>(8, 0),
        info_btn,
    });
    toolbar->setCrossAxisAlignment(CrossAxisAlignment::Center);
    toolbar->setPadding(6.0f);
    toolbar->setGap(0.0f);
    toolbar->setBackgroundColor(Color{0.14f, 0.14f, 0.16f, 1.0f});
    toolbar->setFixedSize(0.0f, 44.0f);
    toolbar->setFlexGrow(1.0f);

    // ── Image area ────────────────────────────────────────────────────────────
    img_area = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{});
    img_area->setMainAxisAlignment(MainAxisAlignment::Center);
    img_area->setCrossAxisAlignment(CrossAxisAlignment::Center);
    img_area->setFlexGrow(1.0f);
    img_area->setBackgroundColor(Color{0.08f, 0.08f, 0.09f, 1.0f});

    // Placeholder before any image is loaded
    auto placeholder = std::make_shared<TextWidget>("Open an image, or drop one here", 14.0f);
    placeholder->setColor(Color{0.56f, 0.56f, 0.60f, 1.0f});   // ≥ 4.5:1 on the dark canvas
    img_area->addChild(placeholder);

    // ── EXIF sidebar ──────────────────────────────────────────────────────────
    info_col = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{});
    info_col->setFixedSize(0.0f, 0.0f); // hidden initially
    info_col->setBackgroundColor(Color{0.12f, 0.12f, 0.15f, 1.0f});
    info_col->setPadding(8.0f);
    info_col->setGap(4.0f);

    // ── Body row ──────────────────────────────────────────────────────────────
    body_row = std::make_shared<FlexRow>(std::vector<std::shared_ptr<Widget>>{
        img_area,
        info_col,
    });
    body_row->setGap(0.0f);
    body_row->setFlexGrow(1.0f);

    // ── Root ──────────────────────────────────────────────────────────────────
    auto root = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{
        toolbar,
        std::make_shared<DividerWidget>(1.0f),
        body_row,
    });
    root->setGap(0.0f);
    root->setBackgroundColor(Color{0.08f, 0.08f, 0.09f, 1.0f});

    // ── Pre-load from command line ────────────────────────────────────────────
    std::string preload;
    // xshell opens files with "--open <path>"; a bare path works too.
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--open") { if (i + 1 < argc) preload = argv[i + 1]; break; }
        if (!a.empty() && a[0] != '-') { preload = a; break; }
    }

    // ── Launch ────────────────────────────────────────────────────────────────
    return XApplication::Run(root, "/tmp/freebsdx.sock", /*sandboxed=*/false,
                             /*is_shell=*/false,
        [preload](XBusClient& xbus) {
            XApplication::setTitle("Image Viewer");

            // Register as MIME handler for common image types
            auto reg_mime = [&](const char* mime) {
                MimeSetDefaultRequest req{};
                std::strncpy(req.mime_type_, mime, sizeof(req.mime_type_) - 1);
                std::strncpy(req.app_id_, "com.freebsdx.imageviewer",
                             sizeof(req.app_id_) - 1);
                xbus.Call("com.freebsdx.MIME",
                          static_cast<uint32_t>(MimeOpcode::SetDefaultHandler),
                          {reinterpret_cast<const uint8_t*>(&req), sizeof(req)},
                          nullptr);
            };
            reg_mime("image/*");
            reg_mime("image/jpeg");
            reg_mime("image/png");
            reg_mime("image/gif");
            reg_mime("image/webp");

            // A drop carries a path this sandbox can't open: ask for it through
            // the picker, starting in its folder.
            XApplication::setOnDrop("text/uri-list",
                [](float, float, const std::string& data) {
                    std::string path = data;
                    while (!path.empty() &&
                           (path.back() == '\n' || path.back() == '\r'))
                        path.pop_back();
                    if (path.starts_with("file://")) path = path.substr(7);
                    if (!path.empty() && isImageFile(path))
                        pick_image(fs::path(path).parent_path().string());
                });

            // The file from the command line, and the rest of its folder. This
            // runs before the sandbox starts, the one time a path can be opened.
            if (!preload.empty() && isImageFile(preload)) {
                fs::path dir = fs::path(preload).parent_path();
                if (dir.empty()) dir = ".";
                dir_fd = ::open(dir.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
                if (dir_fd >= 0) {
                    cap_rights_t rights;
                    cap_rights_init(&rights, CAP_LOOKUP, CAP_READ, CAP_SEEK, CAP_FSTAT);
                    (void)cap_rights_limit(dir_fd, &rights);
                }
                std::vector<std::string> found;
                std::error_code ec;
                for (fs::directory_iterator it(dir, ec), end; !ec && it != end; it.increment(ec))
                    if (it->is_regular_file(ec) && isImageFile(it->path()))
                        found.push_back(it->path().string());
                std::sort(found.begin(), found.end());
                if (std::find(found.begin(), found.end(), preload) == found.end())
                    found.push_back(preload);
                show_files(std::move(found), preload);
            }
        });
}
