/*
 * Animation export encoders — GIF, APNG, ZIP (frame sequence), and video.
 * -----------------------------------------------------------------------
 * All hand-rolled vanilla JS, no dependencies (the project's no-build-step
 * rule). The byte-level encoders (GIF/APNG/ZIP) are pure functions over
 * pixel/byte arrays returning Uint8Array, so they can be unit-tested in
 * Node; only recordVideo() touches the DOM (canvas + MediaRecorder).
 *
 * Format cheat-sheet:
 *  - GIF: universal, palette-based (≤256 colors — fine for pixel art),
 *    binary transparency. We write GIF89a with a global color table and a
 *    standard LZW encoder (ported from the omggif reference logic).
 *  - APNG: lossless + full alpha, plays natively in browsers. The browser
 *    already PNG-encodes each frame for us (canvas.toBlob); we just splice
 *    the frames' IDAT chunks into one file with acTL/fcTL/fdAT chunks.
 *  - ZIP: store-only (no compression — PNGs are already compressed); one
 *    PNG per frame, for video editors / game engines / other art tools.
 *  - Video: MediaRecorder recording a canvas replay of the animation.
 *    Lossy, no transparency; MP4 where the browser supports encoding it,
 *    otherwise WebM.
 */

const Exporters = (() => {
'use strict';

/* ======================================================================
 * Shared helpers
 * ==================================================================== */

/** Growable byte buffer with the little/big-endian writers the formats need. */
function makeBuf() {
  let a = new Uint8Array(4096);
  let n = 0;
  const need = (k) => {
    while (n + k > a.length) {
      const b = new Uint8Array(a.length * 2);
      b.set(a);
      a = b;
    }
  };
  return {
    u8(v) { need(1); a[n++] = v & 255; },
    u16(v) { need(2); a[n++] = v & 255; a[n++] = (v >> 8) & 255; },          // LE (GIF, ZIP)
    u32(v) { need(4); this.u16(v & 0xffff); this.u16((v >>> 16) & 0xffff); }, // LE (ZIP)
    u32be(v) { need(4); a[n++] = (v >>> 24) & 255; a[n++] = (v >>> 16) & 255; a[n++] = (v >>> 8) & 255; a[n++] = v & 255; }, // BE (PNG)
    bytes(b) { need(b.length); a.set(b, n); n += b.length; },
    ascii(s) { need(s.length); for (let i = 0; i < s.length; i++) a[n++] = s.charCodeAt(i); },
    get length() { return n; },
    done() { return a.subarray(0, n); },
  };
}

// Standard CRC-32 (PNG chunks, ZIP entries).
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let i = 0; i < 256; i++) {
    let c = i;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[i] = c;
  }
  return t;
})();

function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 255] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

/* ======================================================================
 * GIF
 * ==================================================================== */

/**
 * Encode frames (arrays of "#rrggbb" | null) as an infinitely-looping GIF.
 * Color index 0 is reserved for transparency; if the art somehow uses more
 * than 255 colors, the rarest are snapped to their nearest kept color.
 */
function encodeGIF(frames, width, height, fps) {
  // --- Build the global color table from actual usage. ---
  const freq = new Map();
  for (const px of frames) {
    for (const c of px) if (c) freq.set(c, (freq.get(c) || 0) + 1);
  }
  const all = [...freq.keys()];
  const kept = all.length > 255
    ? all.sort((a, b) => freq.get(b) - freq.get(a)).slice(0, 255)
    : all;
  const rgb = (c) => [parseInt(c.slice(1, 3), 16), parseInt(c.slice(3, 5), 16), parseInt(c.slice(5, 7), 16)];
  const index = new Map(kept.map((c, i) => [c, i + 1])); // 0 = transparent
  if (all.length > 255) {
    // Snap dropped colors to the visually closest kept one.
    const keptRGB = kept.map(rgb);
    for (const c of all) {
      if (index.has(c)) continue;
      const [r, g, b] = rgb(c);
      let best = 0, bestD = Infinity;
      for (let i = 0; i < keptRGB.length; i++) {
        const d = (keptRGB[i][0] - r) ** 2 + (keptRGB[i][1] - g) ** 2 + (keptRGB[i][2] - b) ** 2;
        if (d < bestD) { bestD = d; best = i; }
      }
      index.set(c, best + 1);
    }
  }

  const numColors = kept.length + 1;
  const gctBits = Math.max(1, Math.ceil(Math.log2(numColors)));
  const gctSize = 1 << gctBits;
  const minCodeSize = Math.max(2, gctBits);
  // GIF delays are hundredths of a second; below 2 most viewers clamp to 10.
  const delay = Math.max(2, Math.round(100 / fps));

  const out = makeBuf();
  out.ascii('GIF89a');
  out.u16(width);
  out.u16(height);
  out.u8(0x80 | 0x70 | (gctBits - 1)); // GCT present, 8-bit color resolution
  out.u8(0);                           // background = index 0
  out.u8(0);                           // no aspect ratio
  for (let i = 0; i < gctSize; i++) {  // global color table (0 = transparent slot)
    const [r, g, b] = i > 0 && i <= kept.length ? rgb(kept[i - 1]) : [0, 0, 0];
    out.u8(r); out.u8(g); out.u8(b);
  }
  // NETSCAPE looping extension: 0 = loop forever.
  out.bytes(new Uint8Array([0x21, 0xff, 0x0b]));
  out.ascii('NETSCAPE2.0');
  out.bytes(new Uint8Array([0x03, 0x01, 0x00, 0x00, 0x00]));

  for (const px of frames) {
    // Graphic Control Extension: disposal 2 (restore to background — makes
    // per-frame transparency actually clear), transparent index 0.
    out.bytes(new Uint8Array([0x21, 0xf9, 0x04, (2 << 2) | 1]));
    out.u16(delay);
    out.u8(0);  // transparent color index
    out.u8(0);  // block terminator
    // Image descriptor: full canvas, no local color table.
    out.u8(0x2c);
    out.u16(0); out.u16(0);
    out.u16(width); out.u16(height);
    out.u8(0);
    const indices = new Uint8Array(px.length);
    for (let i = 0; i < px.length; i++) indices[i] = px[i] ? index.get(px[i]) : 0;
    lzwEncode(minCodeSize, indices, out);
  }
  out.u8(0x3b); // trailer
  return out.done();
}

/** GIF-flavor LZW, packed LSB-first into ≤255-byte sub-blocks. */
function lzwEncode(minCodeSize, indices, out) {
  let bitBuf = 0, bitCnt = 0;
  const block = new Uint8Array(255);
  let blockLen = 0;
  const flushBlock = () => {
    if (!blockLen) return;
    out.u8(blockLen);
    out.bytes(block.subarray(0, blockLen));
    blockLen = 0;
  };
  const emit = (code, size) => {
    bitBuf |= code << bitCnt;
    bitCnt += size;
    while (bitCnt >= 8) {
      block[blockLen++] = bitBuf & 255;
      bitBuf >>>= 8;
      bitCnt -= 8;
      if (blockLen === 255) flushBlock();
    }
  };

  const clear = 1 << minCodeSize;
  const eoi = clear + 1;
  let nextCode = eoi + 1;
  let codeSize = minCodeSize + 1;
  let table = new Map(); // (prefixCode << 8 | pixel) -> code

  out.u8(minCodeSize);
  emit(clear, codeSize);
  let prev = indices[0];
  for (let i = 1; i < indices.length; i++) {
    const k = indices[i];
    const key = (prev << 8) | k;
    const code = table.get(key);
    if (code !== undefined) {
      prev = code;
      continue;
    }
    emit(prev, codeSize);
    if (nextCode === 4096) { // dictionary full: reset, like the reference encoders
      emit(clear, codeSize);
      table = new Map();
      nextCode = eoi + 1;
      codeSize = minCodeSize + 1;
    } else {
      if (nextCode >= (1 << codeSize)) codeSize++;
      table.set(key, nextCode++);
    }
    prev = k;
  }
  emit(prev, codeSize);
  emit(eoi, codeSize);
  while (bitCnt > 0) { // flush the final partial byte(s)
    block[blockLen++] = bitBuf & 255;
    bitBuf >>>= 8;
    bitCnt -= 8;
    if (blockLen === 255) flushBlock();
  }
  flushBlock();
  out.u8(0); // image data terminator
}

/* ======================================================================
 * APNG
 * ==================================================================== */

const PNG_SIG = [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];

/** Split a PNG file into its chunks: [{type, data}] (views, not copies). */
function pngChunks(bytes) {
  for (let i = 0; i < 8; i++) {
    if (bytes[i] !== PNG_SIG[i]) throw new Error('Not a PNG file.');
  }
  const chunks = [];
  let p = 8;
  while (p < bytes.length) {
    const len = (bytes[p] << 24 | bytes[p + 1] << 16 | bytes[p + 2] << 8 | bytes[p + 3]) >>> 0;
    const type = String.fromCharCode(bytes[p + 4], bytes[p + 5], bytes[p + 6], bytes[p + 7]);
    chunks.push({ type, data: bytes.subarray(p + 8, p + 8 + len) });
    p += 12 + len;
  }
  return chunks;
}

/** Write one PNG chunk (length + type + data + CRC over type+data). */
function writeChunk(out, type, data) {
  out.u32be(data.length);
  const crcStart = out.length;
  out.ascii(type);
  out.bytes(data);
  out.u32be(crc32(out.done(), crcStart, out.length));
}

/**
 * Assemble an animated PNG from per-frame PNG files (all the same size, as
 * canvas.toBlob produces). Frame 0's metadata chunks are kept; each frame's
 * compressed image data is spliced in behind fcTL frame-control chunks.
 */
function encodeAPNG(pngs, fps) {
  const frames = pngs.map(pngChunks);
  const first = frames[0];
  const delayNum = Math.max(1, Math.round(1000 / fps)); // fcTL delay = num/den seconds

  const out = makeBuf();
  out.bytes(new Uint8Array(PNG_SIG));

  // Everything before the first IDAT (IHDR, gamma/colorspace chunks, …),
  // with acTL — "this PNG is animated" — inserted right after IHDR.
  for (const ch of first) {
    if (ch.type === 'IDAT') break;
    writeChunk(out, ch.type, ch.data);
    if (ch.type === 'IHDR') {
      const acTL = makeBuf();
      acTL.u32be(frames.length);
      acTL.u32be(0); // 0 = loop forever
      writeChunk(out, 'acTL', acTL.done());
    }
  }

  // fcTL and fdAT share one sequence counter across the whole file.
  let seq = 0;
  const ihdr = first.find((c) => c.type === 'IHDR').data;
  const w = (ihdr[0] << 24 | ihdr[1] << 16 | ihdr[2] << 8 | ihdr[3]) >>> 0;
  const h = (ihdr[4] << 24 | ihdr[5] << 16 | ihdr[6] << 8 | ihdr[7]) >>> 0;

  frames.forEach((chunks, fi) => {
    // Frame control chunk (26 bytes, all big-endian).
    const b = makeBuf();
    b.u32be(seq++);
    b.u32be(w);
    b.u32be(h);
    b.u32be(0); // x
    b.u32be(0); // y
    b.u8(delayNum >> 8); b.u8(delayNum & 255); // delay numerator (u16)
    b.u8(1000 >> 8); b.u8(1000 & 255);         // delay denominator (u16)
    b.u8(0); // dispose_op: none (each frame fully replaces the canvas)
    b.u8(0); // blend_op: source (alpha replaces, no compositing)
    writeChunk(out, 'fcTL', b.done());

    for (const ch of chunks) {
      if (ch.type !== 'IDAT') continue;
      if (fi === 0) {
        // The first frame is also the PNG's static image: plain IDAT.
        writeChunk(out, 'IDAT', ch.data);
      } else {
        // Later frames: same compressed data, wrapped as fdAT with a
        // sequence number prefixed.
        const fd = makeBuf();
        fd.u32be(seq++);
        fd.bytes(ch.data);
        writeChunk(out, 'fdAT', fd.done());
      }
    }
  });

  writeChunk(out, 'IEND', new Uint8Array(0));
  return out.done();
}

/* ======================================================================
 * ZIP (store-only)
 * ==================================================================== */

/**
 * Pack files ([{name, data: Uint8Array}]) into a ZIP with no compression —
 * the entries are PNGs, which are already deflated. Store-only keeps the
 * writer tiny and every unzipper can read it.
 */
function encodeZIP(files) {
  // DOS timestamp of "now" (2-second resolution, like every zip tool).
  const d = new Date();
  const dosTime = (d.getHours() << 11) | (d.getMinutes() << 5) | (d.getSeconds() >> 1);
  const dosDate = ((d.getFullYear() - 1980) << 9) | ((d.getMonth() + 1) << 5) | d.getDate();

  const out = makeBuf();
  const central = [];
  for (const f of files) {
    const crc = crc32(f.data);
    central.push({ name: f.name, crc, size: f.data.length, offset: out.length });
    out.u32(0x04034b50); // local file header
    out.u16(20);         // version needed
    out.u16(0);          // flags
    out.u16(0);          // method: store
    out.u16(dosTime);
    out.u16(dosDate);
    out.u32(crc);
    out.u32(f.data.length); // compressed size (= raw: store)
    out.u32(f.data.length); // uncompressed size
    out.u16(f.name.length);
    out.u16(0);          // extra length
    out.ascii(f.name);
    out.bytes(f.data);
  }

  const cdStart = out.length;
  for (const e of central) {
    out.u32(0x02014b50); // central directory header
    out.u16(20);         // made by
    out.u16(20);         // version needed
    out.u16(0); out.u16(0); // flags, method
    out.u16(dosTime);
    out.u16(dosDate);
    out.u32(e.crc);
    out.u32(e.size);
    out.u32(e.size);
    out.u16(e.name.length);
    out.u16(0); out.u16(0); // extra, comment
    out.u16(0);             // disk number
    out.u16(0);             // internal attrs
    out.u32(0);             // external attrs
    out.u32(e.offset);
    out.ascii(e.name);
  }
  out.u32(0x06054b50); // end of central directory
  out.u16(0); out.u16(0);
  out.u16(files.length);
  out.u16(files.length);
  out.u32(out.length - cdStart - 12); // CD size (12 = EOCD bytes written so far)
  out.u32(cdStart);
  out.u16(0); // comment length
  return out.done();
}

/* ======================================================================
 * Video (MediaRecorder) — browser-only
 * ==================================================================== */

/**
 * Record the animation to a video file by replaying it on an offscreen
 * canvas. Small sprites are integer-upscaled (nearest-neighbor) so codecs
 * have something to work with; transparency becomes a dark background
 * (video has no alpha). Records at least ~1 second by looping short
 * animations. Returns {blob, ext} — mp4 where the browser can encode it,
 * webm otherwise.
 */
async function recordVideo(canvases, width, height, fps, smooth) {
  if (typeof MediaRecorder === 'undefined') {
    throw new Error('This browser cannot record video.');
  }
  const candidates = [
    'video/mp4;codecs=avc1.42E01E',
    'video/mp4',
    'video/webm;codecs=vp9',
    'video/webm;codecs=vp8',
    'video/webm',
  ];
  const mime = candidates.find((m) => MediaRecorder.isTypeSupported(m));
  if (!mime) throw new Error('This browser supports no video format.');

  const scale = Math.max(1, Math.round(480 / Math.max(width, height)));
  const c = document.createElement('canvas');
  c.width = (width * scale + 1) & ~1;   // codecs want even dimensions
  c.height = (height * scale + 1) & ~1;
  const g = c.getContext('2d');
  // Upscaling policy matches the editor's: crisp nearest-neighbor for pixel
  // art, smooth interpolation for freeform (`smooth`) — jaggy edges on
  // painted art would be an artifact of the export, not the artwork.
  g.imageSmoothingEnabled = !!smooth;
  const drawFrame = (i) => {
    g.fillStyle = '#202028';
    g.fillRect(0, 0, c.width, c.height);
    g.drawImage(canvases[i], 0, 0, width * scale, height * scale);
  };

  drawFrame(0);
  const stream = c.captureStream(fps);
  const rec = new MediaRecorder(stream, { mimeType: mime, videoBitsPerSecond: 8e6 });
  const chunks = [];
  rec.ondataavailable = (e) => { if (e.data.size) chunks.push(e.data); };

  const loops = Math.max(1, Math.ceil(fps / canvases.length)); // ≥ ~1s of video
  const total = loops * canvases.length;
  const blob = await new Promise((resolve, reject) => {
    rec.onstop = () => resolve(new Blob(chunks, { type: mime.split(';')[0] }));
    rec.onerror = (e) => reject(e.error || new Error('Recording failed.'));
    rec.start();
    let i = 0;
    const timer = setInterval(() => {
      i++;
      if (i >= total) {
        clearInterval(timer);
        setTimeout(() => rec.stop(), 150); // let the last frame land
        return;
      }
      drawFrame(i % canvases.length);
    }, 1000 / fps);
  });
  stream.getTracks().forEach((t) => t.stop());
  return { blob, ext: mime.startsWith('video/mp4') ? 'mp4' : 'webm' };
}

return { encodeGIF, encodeAPNG, encodeZIP, recordVideo };
})();
