#!/usr/bin/env python3
"""Convert a grayscale vector PDF into a dark-mode vector PDF.

Preserves embedded fonts, selectable text, internal hyperref links,
named destinations, and outline bookmarks by remapping DeviceGray
operators directly in page content streams via MuPDF (`mutool`).
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Dark slate palette tuned for long-form mathematical reading.
# Keys are DeviceGray values in [0.0, 1.0]; values are (r, g, b) in [0.0, 1.0].
BG_RGB = (0.086, 0.094, 0.114)  # #16181D
FG_RGB = (0.894, 0.902, 0.922)  # #E4E6EB

GRAY_PALETTE: list[tuple[float, tuple[float, float, float]]] = [
    (0.0, FG_RGB),                 # #E4E6EB body text, math, borders, filled dots, badges
    (0.5, (0.549, 0.580, 0.651)),  # #8C94A6 secondary diagram edges and tick marks
    (0.6, (0.459, 0.490, 0.565)),  # #757D90 secondary geometry (Figure 7)
    (0.65, (0.384, 0.416, 0.486)), # #626A7C fine fan rays (Figure 5), dashed circle (Figure 7)
    (0.875, (0.180, 0.200, 0.251)),# #2E3340 shaded node set S (Figure 3)
    (0.91, (0.145, 0.161, 0.200)), # #252933 shaded boxes (Figure 1)
    (1.0, BG_RGB),                 # #16181D hollow circles, badge letters, stroke halos
]

NUM_RE = re.compile(rb"^[+-]?(?:\d+\.?\d*|\.\d+)$")
DELIMITERS = set(b" \t\r\n\f\x00()<>[]{}/%")
WHITESPACE = set(b" \t\r\n\f\x00")


def map_gray_to_rgb(gray: float) -> tuple[float, float, float]:
    """Map a DeviceGray value in [0, 1] to dark-mode RGB using piecewise linear lookup."""
    g = min(1.0, max(0.0, gray))
    for stop, rgb in GRAY_PALETTE:
        if abs(g - stop) < 1e-4:
            return rgb
    for (g0, c0), (g1, c1) in zip(GRAY_PALETTE, GRAY_PALETTE[1:]):
        if g0 <= g <= g1:
            t = (g - g0) / (g1 - g0)
            return tuple(c0[i] + t * (c1[i] - c0[i]) for i in range(3))
    return FG_RGB


def fmt_rgb(rgb: tuple[float, float, float]) -> bytes:
    return f"{rgb[0]:.3f} {rgb[1]:.3f} {rgb[2]:.3f}".encode("ascii")


def remap_content_stream(stream: bytes, media_box: tuple[float, float, float, float] | None) -> bytes:
    """Remap DeviceGray g/G operators to DeviceRGB rg/RG while skipping PDF literals."""
    out: list[bytes] = []
    if media_box is not None:
        x0, y0, x1, y1 = media_box
        w = x1 - x0
        h = y1 - y0
        prefix = (
            f"q\n{BG_RGB[0]:.3f} {BG_RGB[1]:.3f} {BG_RGB[2]:.3f} rg\n"
            f"{x0:g} {y0:g} {w:g} {h:g} re f\nQ\n"
            f"{FG_RGB[0]:.3f} {FG_RGB[1]:.3f} {FG_RGB[2]:.3f} rg "
            f"{FG_RGB[0]:.3f} {FG_RGB[1]:.3f} {FG_RGB[2]:.3f} RG\n"
        ).encode("ascii")
        out.append(prefix)

    n = len(stream)
    i = 0
    # Buffer the immediately preceding numeric token and any whitespace after it,
    # so we can rewrite `<gray> g` / `<gray> G` without touching anything else.
    pending_num: bytes | None = None
    pending_ws: bytes = b""

    def flush_pending() -> None:
        nonlocal pending_num, pending_ws
        if pending_num is not None:
            out.append(pending_num)
            out.append(pending_ws)
            pending_num = None
            pending_ws = b""

    while i < n:
        ch = stream[i]

        # Whitespace
        if ch in WHITESPACE:
            j = i + 1
            while j < n and stream[j] in WHITESPACE:
                j += 1
            ws = stream[i:j]
            if pending_num is not None:
                pending_ws += ws
            else:
                out.append(ws)
            i = j
            continue

        # Comment
        if ch == ord("%"):
            flush_pending()
            j = i + 1
            while j < n and stream[j] not in (ord("\r"), ord("\n")):
                j += 1
            out.append(stream[i:j])
            i = j
            continue

        # Literal string (...) with nested parentheses and backslash escapes
        if ch == ord("("):
            flush_pending()
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                c = stream[j]
                if c == ord("\\"):
                    j += 2
                    continue
                if c == ord("("):
                    depth += 1
                elif c == ord(")"):
                    depth -= 1
                j += 1
            out.append(stream[i:j])
            i = j
            continue

        # Hex string <...> or dictionary <<...>>
        if ch == ord("<"):
            flush_pending()
            if i + 1 < n and stream[i + 1] == ord("<"):
                out.append(b"<<")
                i += 2
            else:
                j = stream.find(b">", i + 1)
                j = n if j == -1 else j + 1
                out.append(stream[i:j])
                i = j
            continue

        if ch == ord(">") and i + 1 < n and stream[i + 1] == ord(">"):
            flush_pending()
            out.append(b">>")
            i += 2
            continue

        # Other single-byte delimiters: [, ], {, }, /, ), >
        if ch in DELIMITERS:
            flush_pending()
            if ch == ord("/"):
                j = i + 1
                while j < n and stream[j] not in DELIMITERS:
                    j += 1
                out.append(stream[i:j])
                i = j
            else:
                out.append(stream[i : i + 1])
                i += 1
            continue

        # Regular token (number or operator)
        j = i + 1
        while j < n and stream[j] not in DELIMITERS:
            j += 1
        tok = stream[i:j]
        i = j

        if pending_num is not None and tok in (b"g", b"G"):
            rgb = map_gray_to_rgb(float(pending_num))
            op = b"rg" if tok == b"g" else b"RG"
            out.append(fmt_rgb(rgb) + b" " + op)
            pending_num = None
            pending_ws = b""
        elif NUM_RE.match(tok):
            flush_pending()
            pending_num = tok
            pending_ws = b""
        else:
            flush_pending()
            out.append(tok)

    flush_pending()
    return b"".join(out)


def parse_objects(pdf_bytes: bytes) -> dict[int, tuple[int, int, bytes]]:
    """Return mapping oid -> (start, end, body_bytes) for indirect objects."""
    objs: dict[int, tuple[int, int, bytes]] = {}
    for m in re.finditer(rb"(?:^|[\r\n])(\d+)\s+0\s+obj\b(.*?)endobj", pdf_bytes, re.S):
        oid = int(m.group(1))
        objs[oid] = (m.start(2), m.end(2), m.group(2))
    return objs


def parse_mediabox(body: bytes) -> tuple[float, float, float, float] | None:
    m = re.search(
        rb"/MediaBox\s*\[\s*([+-]?\d*\.?\d+)\s+([+-]?\d*\.?\d+)\s+([+-]?\d*\.?\d+)\s+([+-]?\d*\.?\d+)\s*\]",
        body,
    )
    if not m:
        return None
    return tuple(float(m.group(k)) for k in range(1, 5))


def collect_page_streams(
    objs: dict[int, tuple[int, int, bytes]],
) -> list[tuple[int, tuple[float, float, float, float] | None]]:
    """Walk Catalog -> Pages tree and return (stream_oid, mediabox_or_none) in page order.

    Only the first content stream of each page receives a non-None MediaBox so the
    background rectangle is painted exactly once per page.
    """
    root_pages: int | None = None
    for _, _, body in objs.values():
        if re.search(rb"/Type\s*/Catalog\b", body):
            m = re.search(rb"/Pages\s+(\d+)\s+0\s+R", body)
            if m:
                root_pages = int(m.group(1))
                break
    if root_pages is None:
        raise RuntimeError("Could not locate PDF /Catalog and /Pages root.")

    result: list[tuple[int, tuple[float, float, float, float] | None]] = []

    def walk(oid: int, inherited_mb: tuple[float, float, float, float] | None) -> None:
        _, _, body = objs[oid]
        mb = parse_mediabox(body) or inherited_mb
        if re.search(rb"/Type\s*/Pages\b", body):
            m = re.search(rb"/Kids\s*\[([^\]]+)\]", body, re.S)
            if m:
                for kid in re.findall(rb"(\d+)\s+0\s+R", m.group(1)):
                    walk(int(kid), mb)
        elif re.search(rb"/Type\s*/Page\b", body):
            if mb is None:
                raise RuntimeError(f"Page object {oid} has no /MediaBox.")
            m_single = re.search(rb"/Contents\s+(\d+)\s+0\s+R", body)
            m_array = re.search(rb"/Contents\s*\[([^\]]+)\]", body, re.S)
            stream_ids: list[int] = []
            if m_single:
                stream_ids = [int(m_single.group(1))]
            elif m_array:
                stream_ids = [int(x) for x in re.findall(rb"(\d+)\s+0\s+R", m_array.group(1))]
            for idx, sid in enumerate(stream_ids):
                result.append((sid, mb if idx == 0 else None))

    walk(root_pages, None)
    return result


def rewrite_stream_object(body: bytes, media_box: tuple[float, float, float, float] | None) -> bytes:
    """Remap the stream inside a PDF object body and update its /Length."""
    m = re.search(rb"(stream\r?\n)(.*?)(\r?\nendstream)", body, re.S)
    if not m:
        raise RuntimeError("Expected stream inside page /Contents object.")
    header = body[: m.start(1)]
    new_stream = remap_content_stream(m.group(2), media_box)
    new_header, count = re.subn(
        rb"/Length\s+\d+",
        f"/Length {len(new_stream)}".encode("ascii"),
        header,
        count=1,
    )
    if count != 1:
        raise RuntimeError("Failed to update /Length in stream dictionary.")
    return new_header + m.group(1) + new_stream + m.group(3) + body[m.end(3) :]


def convert_pdf(input_pdf: Path, output_pdf: Path) -> None:
    with tempfile.TemporaryDirectory(prefix="dark_pdf_") as tmp:
        tmp_dir = Path(tmp)
        dec_pdf = tmp_dir / "decompressed.pdf"
        mod_pdf = tmp_dir / "modified.pdf"

        subprocess.run(
            ["mutool", "clean", "-d", str(input_pdf), str(dec_pdf)],
            check=True,
        )

        pdf_bytes = dec_pdf.read_bytes()
        objs = parse_objects(pdf_bytes)
        page_streams = collect_page_streams(objs)
        if not page_streams:
            raise RuntimeError("No page content streams found.")

        # Apply replacements from highest byte offset to lowest to keep offsets valid.
        edits: list[tuple[int, int, bytes]] = []
        seen: set[int] = set()
        for sid, mb in page_streams:
            if sid in seen:
                continue
            seen.add(sid)
            start, end, body = objs[sid]
            edits.append((start, end, rewrite_stream_object(body, mb)))

        edits.sort(key=lambda e: e[0], reverse=True)
        buf = bytearray(pdf_bytes)
        for start, end, replacement in edits:
            buf[start:end] = replacement

        mod_pdf.write_bytes(bytes(buf))
        subprocess.run(
            ["mutool", "clean", "-z", str(mod_pdf), str(output_pdf)],
            check=True,
        )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Convert a grayscale vector PDF into a dark-mode vector PDF."
    )
    parser.add_argument("input", type=Path, help="Path to source light-mode PDF")
    parser.add_argument("output", type=Path, help="Path to destination dark-mode PDF")
    args = parser.parse_args()

    convert_pdf(args.input, args.output)
    return 0


if __name__ == "__main__":
    sys.exit(main())
