/*
 * Sprite Sheet Maker — pixel editor, frames & onion skinning,
 *                      animation preview, export & save/load
 * -----------------------------------------------------------------------
 * Plain JavaScript, no build step. See PROJECT_PLAN.md for the roadmap.
 * (AI frame generation was removed 2026-07-11 — see the progress log.)
 *
 * How the editor works, in one paragraph:
 * The animation is `state.frames`, an array of frame objects. Layers are
 * project-wide (`state.layers` holds name/visibility/order) and each frame
 * carries one "plane" per layer: a flat pixel array (row-major, width*height)
 * where each entry is a hex color string like "#b13e53", or null for a
 * transparent pixel, mirrored onto an offscreen <canvas> that is exactly
 * 1 canvas-pixel per art-pixel. Each frame also owns a COMPOSITE canvas —
 * its visible planes stacked bottom-to-top — which is what rendering,
 * thumbnails, preview, onion skin, and exports all read; editing writes to
 * the active plane and patches the composite per pixel. To draw the screen
 * we blit tinted onion-skin ghosts of the neighboring frames, then the
 * current frame's composite, scaled up by `state.zoom` with image smoothing
 * disabled — which gives crisp nearest-neighbor pixels for free. Zoom/pan
 * are just the scale factor and a pixel offset (`panX`/`panY`); converting
 * a mouse position to an art pixel is a subtract-and-divide.
 */

(() => {
'use strict';

/* ======================================================================
 * Constants & state
 * ==================================================================== */

// Default working palette: "Sweetie 16" by GrafxKid, a popular pixel-art
// palette. Users can add/remove swatches; this is just a good starting set.
const DEFAULT_PALETTE = [
  '#1a1c2c', '#5d275d', '#b13e53', '#ef7d57',
  '#ffcd75', '#a7f070', '#38b764', '#257179',
  '#29366f', '#3b5dc9', '#41a6f6', '#73eff7',
  '#f4f4f4', '#94b0c2', '#566c86', '#333c57',
];

const MAX_UNDO = 100;      // history depth ceiling (see trimHistory — big
                           // entries also shrink the depth via a byte budget
                           // so huge canvases can't blow up memory)
const UNDO_PIXEL_BUDGET = 32 * 1024 * 1024; // total pixels across all snapshots
const MAX_PALETTE = 32;    // oldest auto-added swatch is dropped past this
const MAX_LAYERS = 16;     // per project; every frame carries every layer
const MAX_BRUSH = 64;      // brush/eraser tip side length, in art pixels
const MAX_BRUSH_FREE = 256; // freeform tips can be much larger (HD canvases)
const MIN_ZOOM = 1 / 32;   // screen pixels per art pixel (fractional = zoomed out)
const MAX_ZOOM = 80;
const MAX_W = 7680;        // canvas caps: up to 8K UHD (7680×4320)
const MAX_H = 4320;

const state = {
  // 'pixel' = the classic editor (grid, palette, hex pixels). 'free' =
  // Procreate-style smooth painting (Phase 6). Chosen at New, LOCKED for the
  // life of the project — saved in the project file, never switched in place.
  mode: 'pixel',
  width: 32,
  height: 32,
  frames: [],                        // frame objects — see makeFrame()
  frame: 0,                          // index of the frame being edited
  // Layers are shared across ALL frames (like Aseprite): this array holds the
  // name/visibility/order plus the 6d appearance fields (opacity 0..1, blend
  // mode, alpha lock), and every frame carries one pixel plane per entry.
  // Index 0 is the BOTTOM layer; the panel displays top-first.
  layers: [{ name: 'Layer 1', visible: true, opacity: 1, blend: 'normal', alphaLock: false }],
  layer: 0,                          // index of the layer being edited
  zoom: 16,                          // screen px per art px
  panX: 0, panY: 0,                  // screen position of art pixel (0,0)
  tool: 'brush',                     // 'brush' | 'eraser' | 'fill' | 'eyedropper'
  brushSize: 1,                      // brush/eraser tip side length in art px
  brushShape: 'square',              // 'square' | 'circle' (differs at size ≥ 3)
  brushOpacity: 1,                   // freeform stroke opacity (0..1]
  smudgeStrength: 0.5,               // smudge slider (0..1) — remapped to a stamp alpha by smudgeAlpha()
  brushHardness: 0.8,                // freeform tip edge: 1 = hard, 0 = airbrush (round brush only)
  brush: 'round',                    // active freeform brush id (see PRESET_BRUSHES) — tool state, never saved in projects
  fillTolerance: 0.12,               // freeform fill: how far colors may differ (0..1)
  color: DEFAULT_PALETTE[0],
  palette: DEFAULT_PALETTE.slice(),
  undo: [],                          // stacks of {frame, pixels} snapshots
  redo: [],
  onionPrev: true,                   // ghost the previous frame under the canvas
  onionNext: false,                  // ghost the next frame too (second tint)
  // Procreate-style Animation Assist knobs (Onion… popover in the framebar).
  // View state: persisted per browser in localStorage, never in project files.
  onionFrames: 1,                    // ghosts shown per direction ("onion skin frames")
  onionOpacity: 0.45,                // the NEAREST ghost's alpha; farther ones fade from here
  onionPrevColor: '#ff5a5a',         // tint for frames behind (red — the animation convention)
  onionNextColor: '#5aaaff',         // tint for frames ahead (blue)
  showOrigin: true,                  // crosshair guides through the canvas center
};

/* ======================================================================
 * DOM references & canvases
 * ==================================================================== */

const $ = (id) => document.getElementById(id);

const wrap = $('canvas-wrap');       // container that defines the viewport size
const view = $('view');              // the visible canvas
const ctx = view.getContext('2d');

/**
 * One layer's pixels within one frame ("plane"). In PIXEL mode: a flat pixel
 * array plus an offscreen canvas mirroring it at native resolution (1px =
 * 1 art px; edits update it incrementally) — `src` is a pixel array. In
 * FREEFORM mode the canvas IS the data (full RGBA, `pixels` is null) and
 * `src` is anything drawImage accepts: a decoded save-file Image, or another
 * plane's canvas when duplicating. Undo history identifies planes by object
 * identity, so a plane lives for as long as its frame and layer both exist —
 * never clone one by spreading.
 */
function makePlane(src) {
  const canvas = document.createElement('canvas');
  canvas.width = state.width;
  canvas.height = state.height;
  const c = canvas.getContext('2d');
  if (state.mode === 'free') {
    if (src) c.drawImage(src, 0, 0);
    return { pixels: null, ctx: c, canvas, touched: !!src };
  }
  return {
    pixels: src || new Array(state.width * state.height).fill(null),
    ctx: c,
    canvas,
  };
}

/**
 * A frame bundles one plane per layer (parallel to state.layers) with a
 * COMPOSITE canvas — the visible layers stacked bottom-to-top. Everything
 * that displays a frame (render, preview, thumbnails, onion skin, exports)
 * reads the composite; only editing touches individual planes.
 */
function makeFrame(layerPixels) {
  const canvas = document.createElement('canvas');
  canvas.width = state.width;
  canvas.height = state.height;
  const f = {
    layers: state.layers.map((_, li) => {
      const src = layerPixels ? layerPixels[li] : null;
      const p = makePlane(src);
      if (src && state.mode === 'pixel') repaintLayer(p); // free: makePlane drew it
      return p;
    }),
    ctx: canvas.getContext('2d'),
    canvas,
    thumb: null, // <canvas> in the frame strip; assigned by renderFrames()
    ghost: null, // cached tinted copy for onion skinning — see drawGhost()
  };
  recomposite(f);
  return f;
}

/** The frame currently being edited. */
const cur = () => state.frames[state.frame];
/** The plane being edited: active layer within the current frame. */
const curLayer = () => cur().layers[state.layer];
/** Does one plane contain any art? Freeform planes have no pixel array to
 *  scan, so they track a `touched` flag instead (set by strokes and loads —
 *  it can over-report after an undo, which only costs a needless confirm). */
const planeHasArt = (l) =>
  state.mode === 'free' ? !!l.touched : l.pixels.some((p) => p !== null);
/** Does any layer of any frame contain any art? (guards destructive actions) */
const anyArt = () => state.frames.some((f) => f.layers.some(planeHasArt));

/* ======================================================================
 * Interaction state (not part of the document — never saved)
 * ==================================================================== */

let dpr = 1;                 // devicePixelRatio, so lines stay crisp on HiDPI
let viewW = 0, viewH = 0;    // viewport size in CSS pixels
let hover = null;            // {x,y} art pixel under the cursor, or null
let drawing = false;         // a brush/eraser stroke is in progress
let erasing = false;         // current stroke erases (eraser tool or right-drag)
let strokeChanged = false;   // did the current stroke actually change a pixel?
let lastArt = null;          // previous art position during a stroke (for lines)
let panning = false;
let panAnchor = null;        // {sx, sy, panX, panY} captured when panning starts
let spaceDown = false;       // spacebar held = temporary pan mode
let fitted = false;          // has the initial fit-to-view happened yet?

// --- Selection (Select tool) ---
// A selection starts as a marquee rectangle over the active layer. The first
// move/rotate/flip "lifts" the pixels into `floating` — a free buffer with
// its own grid and offset, drawn above the artwork. PIXEL mode floats stay
// on-grid by construction (whole-pixel offsets, 90°-step transforms).
// FREEFORM floats are a full transform box, Procreate-style: fractional
// x/y/w/h plus `angle` (radians, about the box center), manipulated by drag
// handles. The lifted bitmap (`canvas`, natural size sw×sh) is NEVER
// resampled while editing — the box is just metadata — so any amount of
// fiddling costs exactly one resample, at commit. Committing stamps the
// buffer onto the active layer through the normal undo path.
let selection = null;        // {x, y, w, h} marquee in art coords
let floating = null;         // {pixels, w, h, x, y, canvas, liftEntry, angle, sw, sh}
let selDrag = null;          // {x0, y0} marquee anchor while dragging one out
let floatDrag = null;        // {dx, dy} grab offset while moving the buffer
let xformDrag = null;        // freeform handle drag — see the select pointerdown path
let hoverHandle = null;      // freeform handle under the cursor (hover highlight)
let clipboard = null;        // {pixels, w, h} — survives frame/layer switches

// --- Freeform stroke (free mode's brush/eraser) ---
let stroke = null;           // in-progress stroke state — see beginStroke()
let hoverS = null;           // raw screen cursor position (freeform brush circle)

/* ======================================================================
 * Checkerboard pattern (transparency indicator)
 * ==================================================================== */

// A 16px two-tone tile turned into a repeating fill pattern. It is drawn in a
// translated context in render(), so it stays anchored to the artwork (not the
// screen) and doesn't "swim" when you pan.
const checker = (() => {
  const c = document.createElement('canvas');
  c.width = c.height = 16;
  const g = c.getContext('2d');
  g.fillStyle = '#5a5a63';
  g.fillRect(0, 0, 16, 16);
  g.fillStyle = '#4a4a52';
  g.fillRect(0, 0, 8, 8);
  g.fillRect(8, 8, 8, 8);
  return ctx.createPattern(c, 'repeat');
})();

/* ======================================================================
 * Document / pixel access
 * ==================================================================== */

const inBounds = (x, y) => x >= 0 && y >= 0 && x < state.width && y < state.height;
const idx = (x, y) => y * state.width + x;
const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));

/**
 * Reset to a project of the given size: a single blank frame with one layer
 * by default, or — when loading a saved file — the provided per-layer frame
 * pixels, layer metadata, palette and FPS. `frames` is nested
 * [frame][layer] -> pixel array. Both "New" and "Load" funnel through here.
 */
function newProject(w, h, frames, layersMeta, palette, fpsVal, mode) {
  setPlaying(false);
  // Selection state belongs to the old project; drop it (clipboard survives,
  // so copy-paste across projects works).
  selection = null;
  floating = null;
  selDrag = null;
  floatDrag = null;
  xformDrag = null;
  syncSelectBar();
  state.mode = mode === 'free' ? 'free' : 'pixel';
  state.width = w;
  state.height = h;
  // Appearance fields are optional-with-defaults so pre-6d v3 files (and the
  // plain metas older code paths pass) keep working without a version bump.
  state.layers = (layersMeta || [{ name: 'Layer 1', visible: true }])
    .map((m) => ({
      name: m.name,
      visible: m.visible !== false,
      opacity: typeof m.opacity === 'number' ? clamp(m.opacity, 0, 1) : 1,
      blend: BLEND_MODES.includes(m.blend) ? m.blend : 'normal',
      alphaLock: m.alphaLock === true,
    }));
  state.layer = state.layers.length - 1; // start on the top layer
  state.frames = (frames || [null]).map((fp) => makeFrame(fp));
  state.frame = 0;
  state.undo = [];
  state.redo = [];
  renderLayers();
  if (palette) {
    state.palette = palette;
    renderPalette();
  }
  if (fpsVal) $('inp-fps').value = clamp(fpsVal, 1, 60);
  $('inp-w').value = w;
  $('inp-h').value = h;
  // Keep the preset select honest: show the matching preset if there is one,
  // otherwise fall back to the placeholder.
  const preset = $('sel-preset');
  preset.value = `${w}x${h}`;
  if (preset.selectedIndex === -1) preset.value = '';
  // Mode radios mirror the (possibly loaded) project; preview upscaling is
  // crisp nearest-neighbor for pixel art, smooth interpolation for freeform.
  $('mode-pixel').checked = state.mode === 'pixel';
  $('mode-free').checked = state.mode === 'free';
  preview.classList.toggle('smooth', state.mode === 'free');
  // Mode-specific chrome: opacity/hardness sliders only exist for freeform,
  // square/circle tips only for pixel (freeform tips are always round).
  document.body.classList.toggle('mode-free', state.mode === 'free');
  // The smudge tool and the brush library only exist in freeform.
  if (state.mode !== 'free') {
    if (state.tool === 'smudge') selectTool('brush');
    $('brush-panel').hidden = true;
  }
  $('inp-brush-size').max = maxBrush();
  setBrushSize(state.brushSize); // re-clamp to the mode's tip ceiling
  preview.width = w;  // preview backing store is art-sized; CSS upscales it
  preview.height = h;
  renderFrames();
  fitView();
  updateUI();
}

/* ---- Layer appearance (Phase 6d): opacity, blend modes, alpha lock ---- */

// The blend modes we expose. They map 1:1 onto canvas composite operations
// ('normal' = plain source-over), so stacking layers is still just drawImage.
const BLEND_MODES = ['normal', 'multiply', 'screen', 'overlay'];
const blendOp = (m) => (m.blend === 'normal' ? 'source-over' : m.blend);

/** True while every layer stacks the plain way (opaque, normal blend).
 *  setPixel and the GIF flattener have exact fast paths that are only
 *  correct under this condition — undefined fields fail it safely. */
const layersDefault = () =>
  state.layers.every((m) => m.opacity === 1 && m.blend === 'normal');

// Bulk pixel operations (brush stamps, fills, selection stamps) would pay a
// full rect recomposite PER PIXEL once a layer has opacity/blend. While
// `batching` is set, setPixel just grows this dirty rect and batchPixels()
// recomposites it once at the end.
let batching = false;
let batchRect = null;

/** Run `fn` (a burst of setPixel calls on the CURRENT frame), patching the
 *  composite once over the touched bounds instead of per pixel. With all-
 *  default layers this is a plain call — the per-pixel top-wins patch is
 *  exact there and cheaper than a rect recomposite for small brush tips. */
function batchPixels(fn) {
  if (layersDefault()) { fn(); return; }
  batching = true;
  batchRect = null;
  fn();
  batching = false;
  if (batchRect) patchComposite(cur(), batchRect);
}

/**
 * Write one pixel of the ACTIVE LAYER: data array, the layer's canvas, and
 * the frame's composite. When every layer is default the composite pixel is
 * just the topmost visible color (so erasing reveals layers below); with
 * opacity/blend in play that shortcut is wrong, so the pixel's rect is
 * recomposited honestly (deferred to batchPixels during bulk operations).
 * `color` is a hex string, or null to erase. Out-of-bounds is a no-op, which
 * lets stroke/fill code stay simple. Sets `strokeChanged` so no-op strokes
 * can be dropped from undo history.
 *
 * Alpha lock freezes the layer's transparency: painting can only recolor
 * pixels that already exist, and erasing existing pixels is refused. The
 * selection/clipboard paths pass `ignoreLock` — the lock governs the paint
 * tools, not moves/pastes (and undo bypasses it by swapping whole arrays).
 */
function setPixel(x, y, color, ignoreLock) {
  if (!inBounds(x, y)) return;
  const f = cur();
  const layer = f.layers[state.layer];
  const i = idx(x, y);
  if (!ignoreLock && state.layers[state.layer].alphaLock &&
      (color === null) !== (layer.pixels[i] === null)) return;
  if (layer.pixels[i] === color) return;
  layer.pixels[i] = color;
  strokeChanged = true;
  f.ghost = null; // tinted onion-skin copy is stale now
  layer.ctx.clearRect(x, y, 1, 1);
  if (color) {
    layer.ctx.fillStyle = color;
    layer.ctx.fillRect(x, y, 1, 1);
  }
  if (batching) {
    // Defer the composite: grow the batch's dirty bounds and move on.
    if (!batchRect) {
      batchRect = { x, y, w: 1, h: 1 };
    } else {
      const x1 = Math.max(batchRect.x + batchRect.w, x + 1);
      const y1 = Math.max(batchRect.y + batchRect.h, y + 1);
      batchRect.x = Math.min(batchRect.x, x);
      batchRect.y = Math.min(batchRect.y, y);
      batchRect.w = x1 - batchRect.x;
      batchRect.h = y1 - batchRect.y;
    }
    return;
  }
  if (!layersDefault()) {
    patchComposite(f, { x, y, w: 1, h: 1 });
    return;
  }
  f.ctx.clearRect(x, y, 1, 1);
  for (let li = state.layers.length - 1; li >= 0; li--) {
    if (!state.layers[li].visible) continue;
    const c = f.layers[li].pixels[i];
    if (c) {
      f.ctx.fillStyle = c;
      f.ctx.fillRect(x, y, 1, 1);
      break;
    }
  }
}

/** The color at (x,y): topmost visible layer that has a pixel there. With
 *  layer opacity/blend this is the STORED color, not the blended screen
 *  color — deliberate for the pixel-mode eyedropper, which should pick a
 *  color you can actually paint with, not a blend product. */
function pixelAt(f, x, y) {
  const i = idx(x, y);
  for (let li = state.layers.length - 1; li >= 0; li--) {
    if (!state.layers[li].visible) continue;
    const c = f.layers[li].pixels[i];
    if (c) return c;
  }
  return null;
}

/** A frame flattened to one pixel array (visible layers only) — for GIF export. */
function compositePixels(f) {
  if (state.mode === 'free' || !layersDefault()) {
    // Freeform — or pixel mode once any layer has opacity/blend (stacking
    // hex arrays can't reproduce those) — reads the composite canvas.
    // GIF transparency is 1-bit, so alpha ≥ 128 flattens to opaque
    // (a banding warning lands in 6e).
    const data = f.ctx.getImageData(0, 0, state.width, state.height).data;
    const toHex = (v) => v.toString(16).padStart(2, '0');
    const out = new Array(state.width * state.height).fill(null);
    for (let i = 0; i < out.length; i++) {
      const o = i * 4;
      if (data[o + 3] >= 128) out[i] = `#${toHex(data[o])}${toHex(data[o + 1])}${toHex(data[o + 2])}`;
    }
    return out;
  }
  const out = new Array(state.width * state.height).fill(null);
  for (let li = 0; li < state.layers.length; li++) { // bottom-to-top: top wins
    if (!state.layers[li].visible) continue;
    const px = f.layers[li].pixels;
    for (let i = 0; i < px.length; i++) if (px[i]) out[i] = px[i];
  }
  return out;
}

// "#rrggbb" -> [r, g, b], memoized: repaintLayer calls this once per pixel and
// a frame rarely uses more than a few dozen distinct colors.
const rgbCache = new Map();
function hexToRGB(c) {
  let rgb = rgbCache.get(c);
  if (!rgb) {
    rgb = [parseInt(c.slice(1, 3), 16), parseInt(c.slice(3, 5), 16), parseInt(c.slice(5, 7), 16)];
    rgbCache.set(c, rgb);
  }
  return rgb;
}

/** Rebuild a plane's canvas from its pixel array (after undo/redo/load).
 *  Writes ImageData in one pass — per-pixel fillRect calls would take tens of
 *  seconds at the sizes we now allow. */
function repaintLayer(layer) {
  const img = layer.ctx.createImageData(state.width, state.height);
  const d = img.data;
  for (let i = 0; i < layer.pixels.length; i++) {
    const c = layer.pixels[i];
    if (!c) continue;
    const rgb = hexToRGB(c);
    const o = i * 4;
    d[o] = rgb[0];
    d[o + 1] = rgb[1];
    d[o + 2] = rgb[2];
    d[o + 3] = 255;
  }
  layer.ctx.putImageData(img, 0, 0);
}

/** Rebuild a frame's composite canvas by stacking its visible layers, each
 *  at its own opacity and blend mode (both are native canvas compositing —
 *  the browser blends against everything stacked below, alpha included). */
function recomposite(f) {
  f.ctx.clearRect(0, 0, state.width, state.height);
  state.layers.forEach((m, li) => {
    if (!m.visible) return;
    f.ctx.globalAlpha = m.opacity;
    f.ctx.globalCompositeOperation = blendOp(m);
    f.ctx.drawImage(f.layers[li].canvas, 0, 0);
  });
  f.ctx.globalAlpha = 1;
  f.ctx.globalCompositeOperation = 'source-over';
  f.ghost = null;
}

/** Recomposite every frame + refresh thumbnails (after layer-wide changes). */
function recompositeAll() {
  for (const f of state.frames) {
    recomposite(f);
    updateThumb(f);
  }
  render();
}

/* ======================================================================
 * Coordinate conversion
 * ==================================================================== */

/** Screen (CSS px, viewport-relative) -> art pixel coordinates. May be out of bounds. */
/** Float variant for freeform strokes — sub-pixel positions, no snapping. */
function screenToArtF(sx, sy) {
  return { x: (sx - state.panX) / state.zoom, y: (sy - state.panY) / state.zoom };
}

function screenToArt(sx, sy) {
  return {
    x: Math.floor((sx - state.panX) / state.zoom),
    y: Math.floor((sy - state.panY) / state.zoom),
  };
}

/* ======================================================================
 * Rendering
 * ==================================================================== */

/** Redraw the whole viewport. Cheap at sprite scales; called on any change. */
function render() {
  // Reset transform each frame; dpr scaling means we can think in CSS pixels.
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, viewW, viewH);

  const { panX, panY, zoom } = state;
  const cw = state.width * zoom;   // canvas size on screen
  const ch = state.height * zoom;

  // 1. Checkerboard behind the artwork (transparency indicator).
  //    Translating the context anchors the pattern to the artwork's origin.
  ctx.save();
  ctx.translate(panX, panY);
  ctx.fillStyle = checker;
  ctx.fillRect(0, 0, cw, ch);
  ctx.restore();

  // 2. Onion-skin ghosts of the neighboring frames (tinted so ghost pixels
  //    can't be mistaken for real ones), then the shown frame on top.
  //    Procreate-style reach: up to onionFrames ghosts each direction, drawn
  //    FARTHEST-FIRST so the nearest frame — the one that matters most —
  //    sits on top, each step away fading by ONION_FALLOFF so temporal
  //    distance reads at a glance.
  //    During playback the main canvas IS the player: it shows `playFrame`
  //    instead of the edited frame, and the ghosts follow it around the loop
  //    (they obey the same Ghost prev/next toggles — flip them off for a
  //    clean view). The edited frame is untouched, so pausing with the
  //    button puts you right back where you were working.
  //    Pixel mode scales nearest-neighbor (crisp pixels); freeform smooths.
  const shownIdx = playing ? playFrame : state.frame;
  ctx.imageSmoothingEnabled = state.mode === 'free';
  for (let d = state.onionFrames; d >= 1; d--) {
    const alpha = state.onionOpacity * Math.pow(ONION_FALLOFF, d - 1);
    if (state.onionPrev && shownIdx - d >= 0) {
      drawGhost(state.frames[shownIdx - d], state.onionPrevColor, alpha);
    }
    if (state.onionNext && shownIdx + d < state.frames.length) {
      drawGhost(state.frames[shownIdx + d], state.onionNextColor, alpha);
    }
  }
  ctx.drawImage(state.frames[shownIdx].canvas, panX, panY, cw, ch);

  // 3. Grid lines — pixel mode only. Minor lines per pixel (only useful when
  //    zoomed in); stronger lines every 8 pixels as a sprite-work reference.
  //    Hidden during playback, like the rest of the editing chrome below —
  //    playback is for judging motion, not scaffolding.
  if (state.mode === 'pixel' && !playing) {
    if (zoom >= 8) drawGridLines(1, 'rgba(128, 128, 128, 0.28)');
    if (zoom >= 4) drawGridLines(8, 'rgba(200, 200, 210, 0.30)');
  }

  // 4. Canvas border.
  ctx.strokeStyle = 'rgba(255, 255, 255, 0.5)';
  ctx.lineWidth = 1;
  ctx.strokeRect(panX - 0.5, panY - 0.5, cw + 1, ch + 1);

  // 5. Origin guides: a crosshair through the canvas center. It is the fixed
  //    reference shared by every frame ("are the feet still on this line?").
  if (state.showOrigin && !playing) {
    const ox = Math.round(panX + (state.width / 2) * zoom) + 0.5;
    const oy = Math.round(panY + (state.height / 2) * zoom) + 0.5;
    ctx.strokeStyle = 'rgba(255, 200, 60, 0.45)';
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(ox, panY);
    ctx.lineTo(ox, panY + ch);
    ctx.moveTo(panX, oy);
    ctx.lineTo(panX + cw, oy);
    ctx.stroke();
  }

  // 5.5 Floating selection buffer, then the marquee outline (dashed white
  //     over solid dark so it reads on any background). Freeform floats are
  //     a transform box: content and outline rotate about the box center,
  //     and the Select tool grows resize handles + a rotate knob.
  if (floating && !playing) {
    ctx.imageSmoothingEnabled = state.mode === 'free';
    const f = floating;
    if (f.angle) {
      ctx.save();
      ctx.translate(panX + (f.x + f.w / 2) * zoom, panY + (f.y + f.h / 2) * zoom);
      ctx.rotate(f.angle);
      ctx.drawImage(f.canvas, -f.w / 2 * zoom, -f.h / 2 * zoom, f.w * zoom, f.h * zoom);
      ctx.restore();
    } else {
      ctx.drawImage(f.canvas, panX + f.x * zoom, panY + f.y * zoom,
                    f.w * zoom, f.h * zoom);
    }
  }
  const sel = playing ? null : floating || selection;
  if (sel) {
    // Screen-space corners of the (possibly rotated) box. Unrotated boxes
    // get pixel-center snapping so their 1px outline stays crisp.
    const corners = [[-1, -1], [1, -1], [1, 1], [-1, 1]].map(([hx, hy]) => {
      const v = rotVec(hx * sel.w / 2, hy * sel.h / 2, sel.angle || 0);
      const x = panX + (sel.x + sel.w / 2 + v.x) * zoom;
      const y = panY + (sel.y + sel.h / 2 + v.y) * zoom;
      return sel.angle ? [x, y] : [Math.round(x) + 0.5, Math.round(y) + 0.5];
    });
    const outline = () => {
      ctx.beginPath();
      ctx.moveTo(corners[0][0], corners[0][1]);
      for (const [x, y] of corners.slice(1)) ctx.lineTo(x, y);
      ctx.closePath();
      ctx.stroke();
    };
    ctx.lineWidth = 1;
    ctx.strokeStyle = 'rgba(0, 0, 0, 0.8)';
    outline();
    ctx.strokeStyle = '#ffffff';
    ctx.setLineDash([5, 4]);
    outline();
    ctx.setLineDash([]);

    // Transform handles — freeform Select only (pixel mode keeps its exact
    // 90°-button transforms; free resize would resample pixel art).
    if (state.mode === 'free' && state.tool === 'select') {
      // The handle being dragged — or, at rest, the one under the cursor —
      // draws bigger and accent-blue, so it's obvious what a click will
      // grab before committing to it.
      const active = xformDrag
        ? (xformDrag.kind === 'rotate' ? { rot: true } : xformDrag)
        : hoverHandle;
      const isHot = (hnd) => !!active && (hnd.rot
        ? !!active.rot
        : !active.rot && active.hx === hnd.hx && active.hy === hnd.hy);
      for (const hnd of boxHandles(sel, KNOB_GAP / zoom)) {
        const hot = isHot(hnd);
        const HS = hot ? 6 : 4; // handle half-side, screen px
        const hx = panX + hnd.x * zoom;
        const hy = panY + hnd.y * zoom;
        ctx.fillStyle = hot ? '#41a6f6' : '#ffffff'; // hot = the UI accent
        ctx.strokeStyle = hot ? '#ffffff' : 'rgba(0, 0, 0, 0.8)';
        if (hnd.rot) {
          // Stem from the top edge to the knob, then the knob itself.
          const n = corners[0].map((v, i) => (v + corners[1][i]) / 2);
          ctx.beginPath();
          ctx.moveTo(n[0], n[1]);
          ctx.lineTo(hx, hy);
          ctx.strokeStyle = 'rgba(255, 255, 255, 0.6)';
          ctx.stroke();
          ctx.strokeStyle = hot ? '#ffffff' : 'rgba(0, 0, 0, 0.8)';
          ctx.beginPath();
          ctx.arc(hx, hy, HS + 1.5, 0, Math.PI * 2);
          ctx.fill();
          ctx.stroke();
        } else {
          ctx.fillRect(hx - HS, hy - HS, HS * 2, HS * 2);
          ctx.strokeRect(hx - HS + 0.5, hy - HS + 0.5, HS * 2 - 1, HS * 2 - 1);
        }
      }
    }
  }

  // 6. Cursor. Freeform: a circle matching the tip diameter, at the exact
  //    (unsnapped) pointer position. Pixel mode: outline the actual
  //    brush/eraser footprint (other tools get a single pixel), drawn
  //    edge-by-edge — only edges with no tip pixel on the other side — so
  //    circle tips show their stair-stepped silhouette.
  const brushy = (state.tool === 'brush' || state.tool === 'eraser') && !playing;
  if (playing) {
    // No tool cursor during playback — the pointer is just a pause button.
  } else if (state.mode === 'free') {
    if (hoverS && (brushy || state.tool === 'smudge') && !panning) {
      const r = Math.max((state.brushSize / 2) * zoom, 2);
      ctx.lineWidth = 1;
      ctx.strokeStyle = 'rgba(0, 0, 0, 0.7)';
      ctx.beginPath();
      ctx.arc(hoverS.x, hoverS.y, r + 1, 0, Math.PI * 2);
      ctx.stroke();
      ctx.strokeStyle = 'rgba(255, 255, 255, 0.9)';
      ctx.beginPath();
      ctx.arc(hoverS.x, hoverS.y, r, 0, Math.PI * 2);
      ctx.stroke();
    }
  } else if (hover && zoom * (brushy ? state.brushSize : 1) >= 3) {
    const tip = brushy ? tipOffsets() : [[0, 0]];
    const has = new Set(tip.map(([a, b]) => a + ',' + b));
    const ex = (v) => Math.round(panX + (hover.x + v) * zoom) + 0.5;
    const ey = (v) => Math.round(panY + (hover.y + v) * zoom) + 0.5;
    ctx.strokeStyle = 'rgba(255, 255, 255, 0.9)';
    ctx.lineWidth = 1;
    ctx.beginPath();
    for (const [dx, dy] of tip) {
      if (!has.has((dx - 1) + ',' + dy)) { ctx.moveTo(ex(dx), ey(dy)); ctx.lineTo(ex(dx), ey(dy + 1)); }
      if (!has.has((dx + 1) + ',' + dy)) { ctx.moveTo(ex(dx + 1), ey(dy)); ctx.lineTo(ex(dx + 1), ey(dy + 1)); }
      if (!has.has(dx + ',' + (dy - 1))) { ctx.moveTo(ex(dx), ey(dy)); ctx.lineTo(ex(dx + 1), ey(dy)); }
      if (!has.has(dx + ',' + (dy + 1))) { ctx.moveTo(ex(dx), ey(dy + 1)); ctx.lineTo(ex(dx + 1), ey(dy + 1)); }
    }
    ctx.stroke();
  }

  // render() runs after every change, so this keeps the (stopped) preview
  // mirroring the edited frame live, including mid-stroke.
  updatePreview();
}

/**
 * Draw a frame as an onion-skin "ghost": its opaque pixels re-tinted toward a
 * direction color and faded to `alpha`. The tinted copy is cached on the frame
 * (render() runs on every mouse move, and rebuilding it each time is far too
 * slow at the canvas sizes we now allow); edits to the frame invalidate the
 * cache, and a tint-color change does too (the cache is keyed by tint). Alpha
 * is applied at DRAW time, so the opacity/frames sliders never rebuild caches.
 */
const ONION_FALLOFF = 0.7; // per-step fade: distance d draws at opacity × 0.7^(d−1)
function drawGhost(frame, color, alpha) {
  // 65% pull toward the tint: strong enough that ghost pixels can't be read
  // as real art, weak enough that the art's own shading still shows through.
  const [tr, tg, tb] = hexToRGB(color);
  const tint = `rgba(${tr}, ${tg}, ${tb}, 0.65)`;
  if (!frame.ghost || frame.ghost.tint !== tint) {
    const t = document.createElement('canvas');
    t.width = state.width;
    t.height = state.height;
    const g = t.getContext('2d');
    g.drawImage(frame.canvas, 0, 0);
    g.globalCompositeOperation = 'source-atop'; // tint only where pixels exist
    g.fillStyle = tint;
    g.fillRect(0, 0, t.width, t.height);
    frame.ghost = { tint, canvas: t };
  }
  ctx.globalAlpha = alpha;
  ctx.drawImage(frame.ghost.canvas, state.panX, state.panY,
                state.width * state.zoom, state.height * state.zoom);
  ctx.globalAlpha = 1;
}

/** Stroke vertical+horizontal grid lines every `step` art pixels. Only lines
 *  inside the viewport are drawn — a zoomed-in huge canvas has thousands of
 *  lines total but only a screenful visible. */
function drawGridLines(step, style) {
  const { panX, panY, zoom } = state;
  const left = Math.max(panX, 0);
  const right = Math.min(panX + state.width * zoom, viewW);
  const top = Math.max(panY, 0);
  const bottom = Math.min(panY + state.height * zoom, viewH);
  ctx.strokeStyle = style;
  ctx.lineWidth = 1;
  ctx.beginPath();
  // The +0.5 puts 1px lines on pixel centers so they render crisp, not blurry.
  const x0 = Math.max(step, Math.ceil((left - panX) / zoom / step) * step);
  for (let x = x0; x < state.width; x += step) {
    const sx = Math.round(panX + x * zoom) + 0.5;
    if (sx > right) break;
    ctx.moveTo(sx, top);
    ctx.lineTo(sx, bottom);
  }
  const y0 = Math.max(step, Math.ceil((top - panY) / zoom / step) * step);
  for (let y = y0; y < state.height; y += step) {
    const sy = Math.round(panY + y * zoom) + 0.5;
    if (sy > bottom) break;
    ctx.moveTo(left, sy);
    ctx.lineTo(right, sy);
  }
  ctx.stroke();
}

/* ======================================================================
 * Zoom & pan
 * ==================================================================== */

/**
 * Set the zoom level, keeping the screen point (anchorX, anchorY) fixed over
 * the same art position — i.e. zoom toward/away from the cursor.
 */
function setZoom(newZoom, anchorX, anchorY) {
  newZoom = clamp(newZoom, MIN_ZOOM, MAX_ZOOM);
  const k = newZoom / state.zoom;
  state.panX = anchorX - (anchorX - state.panX) * k;
  state.panY = anchorY - (anchorY - state.panY) * k;
  state.zoom = newZoom;
  updateUI();
  render();
}

/** Center the artwork in the viewport at the largest comfortable zoom.
 *  Whole zooms look crispest, so round down to one when there's room; big
 *  canvases need fractional zoom just to fit on screen at all. */
function fitView() {
  if (!viewW || !viewH) return; // layout hasn't happened yet
  let z = Math.min(viewW / state.width, viewH / state.height) * 0.85;
  if (z >= 1) z = Math.floor(z);
  state.zoom = clamp(z, MIN_ZOOM, MAX_ZOOM);
  state.panX = Math.round((viewW - state.width * state.zoom) / 2);
  state.panY = Math.round((viewH - state.height * state.zoom) / 2);
  updateUI();
  render();
}

/* ======================================================================
 * Undo / redo
 * ==================================================================== */
// Two entry kinds share the undo/redo stacks, distinguished by `.pixels`:
//   pixel mode: {frame, plane, pixels} — a full snapshot of the plane's pixel
//     array before the action. Simple and hard to get wrong; fine at sprite
//     sizes, and the byte budget below caps the damage at huge sizes.
//   freeform:   {frame, plane, rect, before, after} — ImageData patches of
//     just the stroke's bounding box (full-canvas snapshots of an HD RGBA
//     canvas would blow the budget in a couple of strokes).

/** Roughly how many stored pixels an entry costs (patches keep two copies). */
const entryCost = (e) =>
  e.pixels ? e.pixels.length : e.rect.w * e.rect.h * 2;

/** Drop oldest entries once a stack owes more pixels than the budget. */
function trimHistory(stack) {
  let total = 0;
  for (const e of stack) total += entryCost(e);
  while (stack.length > MAX_UNDO || (total > UNDO_PIXEL_BUDGET && stack.length > 1)) {
    total -= entryCost(stack.shift());
  }
}

/** Snapshot the active plane's pixels BEFORE an action mutates them. Clears redo. */
function pushUndo() {
  state.undo.push({ frame: cur(), plane: curLayer(), pixels: curLayer().pixels.slice() });
  trimHistory(state.undo);
  state.redo.length = 0;
}

/** Record a finished freeform stroke (called by finishStroke). Clears redo. */
function pushFreeUndo(entry) {
  state.undo.push(entry);
  trimHistory(state.undo);
  state.redo.length = 0;
  strokeChanged = true; // for symmetry with pixel strokes (status/UI refresh)
}

/** If the action turned out to be a no-op, drop its snapshot again. */
function popUndoIfUnchanged() {
  if (!strokeChanged) state.undo.pop();
}

/**
 * Shared engine for undo and redo: pop entries off `from` until one refers to
 * a frame AND layer that still exist (deleting either orphans its history —
 * those entries are silently skipped), restore the plane's pixels, and jump
 * to that frame + layer so the user can see what changed.
 */
function applyHistory(from, to) {
  commitFloat(); // undoing while floating first lands it (so it's undoable too)
  while (from.length) {
    const entry = from.pop();
    const fi = state.frames.indexOf(entry.frame);
    if (fi === -1) continue; // frame was deleted; its history is dead
    const li = entry.frame.layers.indexOf(entry.plane);
    if (li === -1) continue; // layer was deleted; same deal
    if (entry.pixels) {
      // Pixel-mode entry: swap full pixel-array snapshots.
      to.push({ frame: entry.frame, plane: entry.plane, pixels: entry.plane.pixels });
      entry.plane.pixels = entry.pixels;
      repaintLayer(entry.plane);
    } else {
      // Freeform entry: stamp the appropriate patch back onto the plane. The
      // entry carries both sides, so it just moves between the stacks whole.
      const patch = from === state.undo ? entry.before : entry.after;
      entry.plane.ctx.putImageData(patch, entry.rect.x, entry.rect.y);
      to.push(entry);
    }
    recomposite(entry.frame);
    updateThumb(entry.frame);
    selectFrame(fi);
    selectLayer(li);
    break;
  }
  updateUI();
}

const undo = () => applyHistory(state.undo, state.redo);
const redo = () => applyHistory(state.redo, state.undo);

/* ======================================================================
 * Tools
 * ==================================================================== */

/**
 * The brush/eraser tip as [dx,dy] offsets from the cursor pixel. Size 1 is a
 * single pixel; bigger tips center on the cursor (even sizes extend one extra
 * pixel right/down, like Aseprite). Circle tips keep the pixels whose centers
 * fall inside the tip's inscribed circle — the radius is nudged in slightly so
 * small circles read right (size 3 = a plus, not a full block). Cached per
 * size+shape: strokes call this every stamp, but it only changes with the UI.
 */
let brushTip = { key: '1square', offsets: [[0, 0]] };
function tipOffsets() {
  const n = state.brushSize;
  const key = n + state.brushShape;
  if (brushTip.key === key) return brushTip.offsets;
  const o = Math.floor((n - 1) / 2);   // cursor pixel within the tip
  const r2 = (n / 2 - 0.1) ** 2;
  const offsets = [];
  for (let dy = 0; dy < n; dy++) {
    for (let dx = 0; dx < n; dx++) {
      if (state.brushShape === 'circle' &&
          (dx + 0.5 - n / 2) ** 2 + (dy + 0.5 - n / 2) ** 2 > r2) continue;
      offsets.push([dx - o, dy - o]);
    }
  }
  brushTip = { key, offsets };
  return offsets;
}

/** Stamp the whole brush tip at one art position (setPixel bounds-checks). */
function paintStamp(x, y, color) {
  batchPixels(() => {
    for (const [dx, dy] of tipOffsets()) setPixel(x + dx, y + dy, color);
  });
}

/** Paint a line of brush stamps between two art points (Bresenham), so fast
 *  mouse movement leaves a continuous stroke instead of scattered dots. */
function paintLine(x0, y0, x1, y1, color) {
  const dx = Math.abs(x1 - x0);
  const dy = -Math.abs(y1 - y0);
  const sx = x0 < x1 ? 1 : -1;
  const sy = y0 < y1 ? 1 : -1;
  let err = dx + dy;
  for (;;) {
    paintStamp(x0, y0, color);
    if (x0 === x1 && y0 === y1) break;
    const e2 = 2 * err;
    if (e2 >= dy) { err += dy; x0 += sx; }
    if (e2 <= dx) { err += dx; y0 += sy; }
  }
}

/** Flood fill the contiguous region containing (x,y) ON THE ACTIVE LAYER —
 *  contiguity is judged by that layer's own pixels, so filling "transparent"
 *  areas of a top layer works even when lower layers show through. `color`
 *  may be null (right-click fill = fill with transparency). */
function floodFill(x, y, color) {
  if (!inBounds(x, y)) return;
  const px = curLayer().pixels;
  const target = px[idx(x, y)];
  if (target === color) return; // filling with the same color = no-op
  // Alpha lock: contiguity is exact-value, so the whole region shares the
  // target's transparency — a fill that would change it is wholly blocked.
  // Bail BEFORE flooding: setPixel would refuse every write, leaving each
  // pixel still matching `target`, and the traversal would never terminate.
  if (state.layers[state.layer].alphaLock && (target === null) !== (color === null)) {
    flashHint('Layer alpha is locked — this fill would change transparency.');
    return;
  }
  batchPixels(() => {
    const stack = [[x, y]];
    while (stack.length) {
      const [cx, cy] = stack.pop();
      if (!inBounds(cx, cy) || px[idx(cx, cy)] !== target) continue;
      setPixel(cx, cy, color);
      stack.push([cx + 1, cy], [cx - 1, cy], [cx, cy + 1], [cx, cy - 1]);
    }
  });
}

/** Pick the color VISIBLE under (x,y) — i.e. from the composite, whatever
 *  layer it lives on — as the current color. Transparent = no-op. */
function eyedrop(x, y) {
  if (!inBounds(x, y)) return;
  let c = null;
  if (state.mode === 'free') {
    const d = cur().ctx.getImageData(x, y, 1, 1).data; // composite = what you see
    if (d[3]) {
      const toHex = (v) => v.toString(16).padStart(2, '0');
      c = `#${toHex(d[0])}${toHex(d[1])}${toHex(d[2])}`;
    }
  } else {
    c = pixelAt(cur(), x, y);
  }
  if (c) selectColor(c);
}

/**
 * Freeform flood fill: tolerance-based, on the active plane's RGBA data.
 * Soft brush edges mean exact-match filling would leave halos, so pixels
 * within `state.fillTolerance` of the clicked color (per channel) flow too.
 * A transparent seed matches by alpha alone — the RGB under alpha 0 is
 * leftover garbage from erased strokes and must not split the region.
 * `color` null = fill with transparency (right-click, like pixel mode).
 * Hard edges (no anti-aliasing); undo = one dirty-rect patch.
 */
function freeFill(x, y, color) {
  if (!inBounds(x, y)) return;
  const w = state.width;
  const h = state.height;
  const plane = curLayer();
  const frame = cur();
  const img = plane.ctx.getImageData(0, 0, w, h);
  const data = img.data;
  const orig = new Uint8ClampedArray(data); // pre-fill copy, for undo
  const o0 = (y * w + x) * 4;
  const tr = data[o0], tg = data[o0 + 1], tb = data[o0 + 2], ta = data[o0 + 3];
  // Alpha lock: the fill recolors but keeps every pixel's coverage (see the
  // write below). Filling with transparency, or color into a transparent
  // region, could then never change anything visible — block with a hint.
  const lock = state.layers[state.layer].alphaLock;
  if (lock && (!color || ta === 0)) {
    flashHint('Layer alpha is locked — this fill would change transparency.');
    return;
  }
  const [rr, rg, rb] = color ? hexToRGB(color) : [0, 0, 0];
  const ra = color ? 255 : 0;
  if (tr === rr && tg === rg && tb === rb && ta === ra) return; // no-op
  const tol = Math.round(state.fillTolerance * 255);
  const match = (i) => {
    const o = i * 4;
    if (ta === 0) return data[o + 3] <= tol;
    return Math.abs(data[o] - tr) <= tol && Math.abs(data[o + 1] - tg) <= tol &&
           Math.abs(data[o + 2] - tb) <= tol && Math.abs(data[o + 3] - ta) <= tol;
  };

  const visited = new Uint8Array(w * h);
  const stack = [y * w + x];
  visited[y * w + x] = 1;
  let bx0 = x, by0 = y, bx1 = x, by1 = y; // filled region's bounding box
  while (stack.length) {
    const i = stack.pop();
    const px = i % w;
    const py = (i / w) | 0;
    const o = i * 4;
    data[o] = rr; data[o + 1] = rg; data[o + 2] = rb;
    if (!lock) data[o + 3] = ra; // locked = recolor only, coverage stays
    if (px < bx0) bx0 = px; else if (px > bx1) bx1 = px;
    if (py < by0) by0 = py; else if (py > by1) by1 = py;
    if (px > 0 && !visited[i - 1] && match(i - 1)) { visited[i - 1] = 1; stack.push(i - 1); }
    if (px < w - 1 && !visited[i + 1] && match(i + 1)) { visited[i + 1] = 1; stack.push(i + 1); }
    if (py > 0 && !visited[i - w] && match(i - w)) { visited[i - w] = 1; stack.push(i - w); }
    if (py < h - 1 && !visited[i + w] && match(i + w)) { visited[i + w] = 1; stack.push(i + w); }
  }

  const r = { x: bx0, y: by0, w: bx1 - bx0 + 1, h: by1 - by0 + 1 };
  const subImage = (src) => { // one rect of a full-canvas RGBA array
    const out = plane.ctx.createImageData(r.w, r.h);
    for (let yy = 0; yy < r.h; yy++) {
      const so = ((r.y + yy) * w + r.x) * 4;
      out.data.set(src.subarray(so, so + r.w * 4), yy * r.w * 4);
    }
    return out;
  };
  plane.ctx.putImageData(img, 0, 0, r.x, r.y, r.w, r.h); // dirty rect only
  plane.touched = true;
  pushFreeUndo({ frame, plane, rect: r, before: subImage(orig), after: subImage(data) });
  patchComposite(frame, r);
  updateThumb(frame);
  drawLayerThumb(state.layer);
  updateUI();
  render();
}

/* ======================================================================
 * Freeform stroke engine (Phase 6b) — free mode's brush & eraser
 * ==================================================================== */
// A stroke stamps a round tip along the (streamline-smoothed) pointer path
// into a full-strength STROKE BUFFER, which is composited over the plane at
// the brush opacity — so overlapping stamps within one stroke never build up
// past the opacity setting (the Procreate behavior). A PREVIEW canvas holds
// plane+buffer merged live, and the frame's composite is patched from it per
// move, so the screen and the animation preview show the stroke as it
// happens (including erasing). On pointer-up the preview's dirty rect
// becomes the plane's new content, and a before/after ImageData pair goes
// into undo history.

const STAMP_SPACING = 0.15; // gap between stamps, as a fraction of tip diameter
// Smudge stamps much tighter: at paint spacing each deposit's soft rim reads
// as a ring and the trail looks like a stack of coins. The per-stamp rates
// are renormalized in beginStroke so the overall strength stays the same.
const SMUDGE_SPACING = 0.05;
const STREAMLINE = 0.35;    // how far the smoothed point chases the cursor per event

/** Stylus pressure (0..1]. Mice report a constant, so they paint at full. */
const penPressure = (e) => (e.pointerType === 'pen' ? e.pressure || 0.5 : 1);

/* ---- Brush library (Phase 7): round + texture tips, imports, smudge ---- */

// Texture masks are generated (and imports normalized) at this size, then
// scaled at stamp time — one mask serves every brush size.
const TIP_SIZE = 128;

/** Tiny seeded PRNG (mulberry32) so the preset textures come out identical
 *  every session — a brush that changed its grain on reload would feel
 *  broken. Returns a () => [0,1) function. */
function makeRng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/**
 * The texture generators: each returns an n×n alpha map (0 outside the tip's
 * disc) for one preset. Pure — no canvas, no state — so the Node suite can
 * assert on their character (coverage, streakiness) without real pixels.
 */
function textureAlpha(gen, n, rng) {
  const a = new Uint8ClampedArray(n * n);
  const r = n / 2;
  // Distance falloff: 1 well inside the disc, easing to 0 at the rim, so no
  // texture ends in a hard circular cookie-cutter edge.
  const falloff = (x, y) => {
    const d = Math.hypot(x - r + 0.5, y - r + 0.5) / r;
    return d >= 1 ? 0 : Math.min(1, (1 - d) * 4);
  };
  const dot = (cx, cy, rad, alpha) => {
    // A soft-edged dot, clipped to the disc via the falloff.
    for (let y = Math.floor(cy - rad); y <= cy + rad; y++) {
      for (let x = Math.floor(cx - rad); x <= cx + rad; x++) {
        if (x < 0 || y < 0 || x >= n || y >= n) continue;
        const d = Math.hypot(x - cx, y - cy) / rad;
        if (d >= 1) continue;
        const v = alpha * (1 - d * d) * falloff(x, y);
        const i = y * n + x;
        if (v > a[i]) a[i] = v;
      }
    }
  };

  if (gen === 'chalk') {
    // Dry-media grain: every pixel gets skewed random alpha — mostly faint,
    // some strong — so strokes look dusty rather than flat.
    for (let y = 0; y < n; y++) {
      for (let x = 0; x < n; x++) {
        a[y * n + x] = 255 * rng() ** 1.7 * falloff(x, y);
      }
    }
  } else if (gen === 'spray') {
    // Sparse splatter: droplets biased toward the center (sqrt keeps the
    // distribution disc-uniform, the 0.8 pulls it inward).
    for (let k = 0; k < n * n * 0.02; k++) {
      const ang = rng() * Math.PI * 2;
      const dist = Math.sqrt(rng()) * 0.8 * r;
      dot(r + Math.cos(ang) * dist, r + Math.sin(ang) * dist,
          1 + rng() * n * 0.02, 120 + rng() * 135);
    }
  } else if (gen === 'bristle') {
    // Parallel streaks, like a dry brush dragged sideways: horizontal bands
    // of random thickness/strength with ragged per-pixel dropout. The brush
    // meta sets follow=true so the streaks align with the stroke direction.
    let y = 0;
    while (y < n) {
      const th = 1 + Math.floor(rng() * 3);          // streak thickness
      const strength = rng() < 0.25 ? 0 : 90 + rng() * 165; // some gaps
      for (let dy = 0; dy < th && y + dy < n; dy++) {
        for (let x = 0; x < n; x++) {
          const v = strength * (0.6 + 0.4 * rng()) * falloff(x, y + dy);
          if (rng() > 0.15) a[(y + dy) * n + x] = v;
        }
      }
      y += th + Math.floor(rng() * 2);
    }
  } else if (gen === 'stipple') {
    // Fine, even tooth: a jittered grid of small soft dots — paper grain.
    const step = n / 16;
    for (let gy = 0; gy < 16; gy++) {
      for (let gx = 0; gx < 16; gx++) {
        dot(gx * step + rng() * step, gy * step + rng() * step,
            step * (0.3 + rng() * 0.35), 150 + rng() * 105);
      }
    }
  }
  return a;
}

// The brush library. `round` is the classic disc driven by the hardness
// slider; texture brushes stamp a tinted mask with per-stamp dynamics:
// rotJitter (fraction of a half-turn of random rotation), sizeJitter
// (± fraction of the tip size), follow (base rotation tracks the stroke's
// travel direction — bristle streaks should run along the stroke).
// Imported brushes (Phase 7 UI) append here with `imported: true`.
const PRESET_BRUSHES = [
  { id: 'round',   name: 'Round',   kind: 'round' },
  { id: 'chalk',   name: 'Chalk',   kind: 'texture', gen: 'chalk',   seed: 7,  rotJitter: 1,    sizeJitter: 0.15, follow: false },
  { id: 'spray',   name: 'Spray',   kind: 'texture', gen: 'spray',   seed: 13, rotJitter: 1,    sizeJitter: 0.25, follow: false },
  { id: 'bristle', name: 'Bristle', kind: 'texture', gen: 'bristle', seed: 3,  rotJitter: 0.06, sizeJitter: 0.1,  follow: true },
  { id: 'stipple', name: 'Stipple', kind: 'texture', gen: 'stipple', seed: 29, rotJitter: 1,    sizeJitter: 0.1,  follow: false },
];
let brushes = PRESET_BRUSHES.slice();

const curBrush = () => brushes.find((b) => b.id === state.brush) || brushes[0];

/** A brush's white-on-transparent mask canvas (presets generate lazily;
 *  imported brushes arrive with `mask` already set). */
function brushMask(b) {
  if (!b.mask) {
    const alpha = textureAlpha(b.gen, TIP_SIZE, makeRng(b.seed));
    const c = document.createElement('canvas');
    c.width = c.height = TIP_SIZE;
    const g = c.getContext('2d');
    const img = g.createImageData(TIP_SIZE, TIP_SIZE);
    for (let i = 0; i < alpha.length; i++) {
      const o = i * 4;
      img.data[o] = img.data[o + 1] = img.data[o + 2] = 255;
      img.data[o + 3] = alpha[i];
    }
    g.putImageData(img, 0, 0);
    b.mask = c;
  }
  return b.mask;
}

/** Build a tip canvas for any brush/color — round discs render at `d` px
 *  (crisp gradient), texture tips tint the TIP_SIZE mask (scaled at stamp
 *  time). Uncached: freeTip caches the hot path, previews call this raw. */
function buildTip(b, color, d, hardness) {
  const c = document.createElement('canvas');
  const g = c.getContext('2d');
  if (b.kind === 'round') {
    c.width = c.height = d;
    const r = d / 2;
    const [cr, cg, cb] = hexToRGB(color);
    const grad = g.createRadialGradient(r, r, 0, r, r, r);
    grad.addColorStop(0, `rgba(${cr},${cg},${cb},1)`);
    grad.addColorStop(clamp(hardness, 0, 0.99), `rgba(${cr},${cg},${cb},1)`);
    grad.addColorStop(1, `rgba(${cr},${cg},${cb},0)`);
    g.fillStyle = grad;
    g.fillRect(0, 0, d, d);
    return c;
  }
  // Texture: keep the mask's alpha, replace its color with the paint color.
  c.width = c.height = TIP_SIZE;
  g.drawImage(brushMask(b), 0, 0);
  g.globalCompositeOperation = 'source-in';
  g.fillStyle = color;
  g.fillRect(0, 0, TIP_SIZE, TIP_SIZE);
  return c;
}

// The active tip, rebuilt only when brush / size / hardness / color change.
// The eraser and the smudge grab-mask use only the tip's alpha.
let tipCache = { key: '', canvas: null };
function freeTip(color) {
  const b = curBrush();
  const d = Math.max(2, state.brushSize);
  const key = `${b.id}|${d}|${state.brushHardness}|${color}`;
  if (tipCache.key !== key) {
    tipCache = { key, canvas: buildTip(b, color, d, state.brushHardness) };
  }
  return tipCache.canvas;
}

/** Grow a float rect {x0,y0,x1,y1} to cover another box (null = first box). */
const growRect = (r, x0, y0, x1, y1) => (r
  ? { x0: Math.min(r.x0, x0), y0: Math.min(r.y0, y0),
      x1: Math.max(r.x1, x1), y1: Math.max(r.y1, y1) }
  : { x0, y0, x1, y1 });

/** Clamp a float rect to the canvas as {x,y,w,h} ints; null if fully outside. */
function clampRect(r) {
  if (!r) return null;
  const x = Math.max(0, Math.floor(r.x0));
  const y = Math.max(0, Math.floor(r.y0));
  const x1 = Math.min(state.width, Math.ceil(r.x1));
  const y1 = Math.min(state.height, Math.ceil(r.y1));
  return x1 > x && y1 > y ? { x, y, w: x1 - x, h: y1 - y } : null;
}

/**
 * Where to stamp along one path segment, honoring the inter-stamp spacing
 * carried over from the previous segment (`rem`), so stroke density doesn't
 * depend on pointer speed. PURE — returns [x, y, pressure] triples plus the
 * leftover distance for the next segment. (Unit-tested headlessly.)
 */
function stampPositions(x0, y0, x1, y1, p0, p1, size, rem, spacing = STAMP_SPACING) {
  const stamps = [];
  const dist = Math.hypot(x1 - x0, y1 - y0);
  let at = rem;
  while (at <= dist) {
    const t = dist ? at / dist : 0;
    const p = p0 + (p1 - p0) * t;
    stamps.push([x0 + (x1 - x0) * t, y0 + (y1 - y0) * t, p]);
    at += Math.max(0.4, size * p * spacing);
  }
  return { stamps, rem: at - dist };
}

/** The smudge Strength slider (0..1) → per-stamp alpha. Carry-over compounds
 *  stamp after stamp, so smear length grows roughly geometrically with the
 *  alpha — a linear slider crowds all the feel into its top few percent.
 *  The inverted-square ease spreads it back out: the low end stays a gentle
 *  blur, the top end reaches alpha 1 (every stamp re-deposits its whole
 *  grab, dragging color as far as the stroke goes). */
const smudgeAlpha = () => 1 - (1 - state.smudgeStrength) ** 2;

/** Start a freeform stroke at a (float) art position. `smudge` strokes
 *  deposit no color of their own — see smudgeStamp(). */
function beginStroke(x, y, pressure, erase, smudge) {
  const preview = document.createElement('canvas');
  preview.width = state.width;
  preview.height = state.height;
  // Smudge reads the preview back every stamp (getImageData) — tell the
  // browser up front so it keeps the canvas off the GPU. The option only
  // counts on the FIRST getContext call for a canvas, so it happens here.
  const prevCtx = preview.getContext('2d', { willReadFrequently: smudge });
  // Seed the preview with the WHOLE plane. refreshStroke() only re-merges the
  // regions the stroke passes through, but finishStroke() stamps the stroke's
  // entire bounding box back onto the plane — any part of that box the stroke
  // never touched must hold plane content, not transparency, or committing
  // the stroke would erase existing art around it.
  prevCtx.drawImage(curLayer().canvas, 0, 0);
  let buf = null;
  if (!smudge) {
    buf = document.createElement('canvas');
    buf.width = state.width;
    buf.height = state.height;
  }
  stroke = {
    frame: cur(),                 // pinned: switching frames mid-stroke must
    plane: curLayer(),            // not retarget the merge
    buf, bufCtx: buf && buf.getContext('2d'),
    preview, prevCtx,
    erase,
    smudge,
    tips: smudge ? new Map() : null, // smudge: sub-pixel tip rasters, per stroke
    carry: null,                  // smudge: premultiplied float RGBA "paint on
    carryBase: 0,                 //   the finger" — never quantized to 8-bit
    angle: 0,                     // stroke travel direction (for follow tips)
    // Alpha lock, pinned at stroke start: the buffer merges with source-atop
    // instead of source-over, so paint lands only where the plane already
    // has alpha (and exactly at that alpha — atop preserves dest coverage).
    // Smudge preserves alpha differently — see finishStroke().
    lock: state.layers[state.layer].alphaLock,
    // Paint/erase strokes composite at the Opacity slider; smudge carries
    // pixels at its own Strength slider (opacity is meaningless for a tool
    // that deposits no color).
    opacity: smudge ? smudgeAlpha() : state.brushOpacity,
    // Smudge exchange rates, renormalized for its tighter stamp spacing so
    // 1/k stamps at these rates compose to one stamp at the slider's rate.
    // Pickup is Strength's inverse — a light touch reloads the finger almost
    // instantly (barely smears), a heavy one holds paint across a long drag —
    // floored so the finger always exchanges and a smear can run out clear.
    deposit: 0, pickup: 0,
    color: erase ? '#ffffff' : state.color, // eraser only uses the alpha
    x, y,                         // streamline-smoothed position
    pressure,
    rem: 0,                       // distance until the next stamp is due
    rect: null,                   // whole-stroke dirty rect (float, art px)
    seg: null,                    // this event's dirty rect — reset per move
  };
  if (smudge) {
    const k = SMUDGE_SPACING / STAMP_SPACING;
    const s = stroke.opacity;
    stroke.deposit = 1 - (1 - s) ** k;
    stroke.pickup = Math.max(0.008, 1 - s ** k);
  }
  stamp(x, y, pressure);          // a click with no drag still leaves a dot
  refreshStroke();
}

/** One tip stamp; pressure scales the diameter. Texture brushes land each
 *  stamp with their per-stamp dynamics (rotation/size jitter, optionally
 *  aligned to the stroke direction) so the texture never reads as a
 *  repeating pattern; smudge stamps drag pixels instead of depositing. */
function stamp(x, y, pressure) {
  const d = Math.max(1, state.brushSize * pressure);
  if (stroke.smudge) {
    smudgeStamp(x, y, d);
    return;
  }
  const b = curBrush();
  const g = stroke.bufCtx;
  let reach = d / 2 + 1;
  if (b.kind === 'texture') {
    const s = d * (1 + (Math.random() * 2 - 1) * b.sizeJitter);
    const ang = (b.follow ? stroke.angle : 0) +
                (Math.random() * 2 - 1) * Math.PI * b.rotJitter;
    g.save();
    g.translate(x, y);
    g.rotate(ang);
    g.drawImage(freeTip(stroke.color), -s / 2, -s / 2, s, s);
    g.restore();
    reach = (s * Math.SQRT2) / 2 + 1; // a rotated square reaches its diagonal
  } else {
    g.drawImage(freeTip(stroke.color), x - d / 2, y - d / 2, d, d);
  }
  stroke.rect = growRect(stroke.rect, x - reach, y - reach, x + reach, y + reach);
  stroke.seg = growRect(stroke.seg, x - reach, y - reach, x + reach, y + reach);
}

/**
 * One smudge stamp — the wet-finger model (same shape as Krita/Procreate):
 * the stroke carries a float "paint on the finger" buffer (`stroke.carry`,
 * PREMULTIPLIED RGBA 0..1). Each stamp DEPOSITS a convex mix of finger-over-
 * surface at the Strength rate, then the finger PICKS UP some of the surface
 * it just touched. Dragging over empty canvas dilutes the finger toward
 * transparent, so a smear that runs out of paint fades to CLEAR.
 *
 * Two hard-won invariants live here:
 * - The carry NEVER round-trips through the canvas. Canvas storage is 8-bit
 *   premultiplied, and at low alpha it quantizes colors to extremes (stored
 *   (3,0,0,α3) reads back as pure (255,0,0)); earlier smudge versions pushed
 *   the traveling patch through that mill every stamp and long drags washed
 *   out to white. Deposits are convex combinations, so the trail can only
 *   move BETWEEN the surface color and the finger color — white can't appear.
 * - Patches are integer-aligned (exact reads/writes, no resampling) but the
 *   TIP MASK is rasterized at the stamp's sub-pixel offset. Snapping the mask
 *   to whole pixels too gave hard stamp edges a ±1px sawtooth trail.
 */
function smudgeStamp(x, y, d) {
  const reach = d / 2 + 2;
  stroke.rect = growRect(stroke.rect, x - reach, y - reach, x + reach, y + reach);
  stroke.seg = growRect(stroke.seg, x - reach, y - reach, x + reach, y + reach);
  const base = Math.max(1, Math.round(d));
  const w = base + 1;                    // room for the sub-pixel tip shift
  const left = x - base / 2, top = y - base / 2;
  const px0 = Math.floor(left), py0 = Math.floor(top);
  const tip = smudgeTip(base, left - px0, top - py0);
  const g = stroke.prevCtx;
  const img = g.getImageData(px0, py0, w, w); // off-canvas reads: transparent
  if (!stroke.carry || stroke.carryBase !== base) {
    // First stamp (or pen pressure resized the tip): load the finger with
    // EXACTLY what's under it — no tip masking — and deposit nothing yet.
    // The tip already gates the exchange rates inside smudgeMix; masking the
    // content too would load a faded copy of the surface, and depositing
    // that is a partial ERASE — a click (or the jitter inside one) visibly
    // thinned solid color. With an exact load, finger == surface is a
    // fixed point: nothing changes until a real drag misaligns them.
    const c = new Float32Array(w * w * 4);
    const D = img.data;
    for (let i = 0, px = 0; i < D.length; i += 4, px++) {
      const a = D[i + 3] / 255;
      c[px * 4]     = (D[i] / 255) * a;
      c[px * 4 + 1] = (D[i + 1] / 255) * a;
      c[px * 4 + 2] = (D[i + 2] / 255) * a;
      c[px * 4 + 3] = a;
    }
    stroke.carry = c;
    stroke.carryBase = base;
    return;
  }
  smudgeMix(img.data, stroke.carry, tip, stroke.deposit, stroke.pickup);
  g.putImageData(img, px0, py0);
}

/** The active tip's alpha as a Float32Array (0..1), rasterized at diameter
 *  `base` inside a (base+1)² patch, shifted by the stamp's sub-pixel offset.
 *  Cached per stroke at 1/8-px granularity (≤64 variants per size). */
function smudgeTip(base, fx, fy) {
  const key = base + ':' + Math.round(fx * 8) + ':' + Math.round(fy * 8);
  let t = stroke.tips.get(key);
  if (!t) {
    const w = base + 1;
    const c = document.createElement('canvas');
    c.width = c.height = w;
    const g = c.getContext('2d');
    g.drawImage(freeTip('#ffffff'), fx, fy, base, base); // color irrelevant — alpha shapes the tip
    const a = g.getImageData(0, 0, w, w).data;
    t = new Float32Array(w * w);
    for (let i = 0; i < t.length; i++) t[i] = a[i * 4 + 3] / 255;
    stroke.tips.set(key, t);
  }
  return t;
}

/**
 * One finger↔surface exchange. `D` is the canvas patch (straight RGBA bytes,
 * mutated); `carry` the finger (premultiplied float RGBA 0..1, mutated);
 * `tip` the mask; `s` the deposit rate (eased Strength); `p` the pickup rate.
 * Deposit first (surface moves toward finger), then pickup (finger moves
 * toward the freshly deposited surface — the FLOAT value, pre-rounding, so
 * quantization never feeds back into what the finger carries). All mixes are
 * convex, so surface and finger only ever move between each other's values:
 * identical content is a byte-exact fixed point, and a finger dragged over
 * emptiness decays to transparent. Pure; exported through the test hook.
 */
function smudgeMix(D, carry, tip, s, p) {
  for (let i = 0, j = 0, px = 0; i < D.length; i += 4, j += 4, px++) {
    const t = tip[px];
    if (t <= 0) continue;
    const r = t * s;      // deposit rate, faded at the tip's soft rim
    const q = t * p;      // pickup rate, likewise
    const da = D[i + 3] / 255;
    const dr = (D[i] / 255) * da;      // surface, premultiplied
    const dg = (D[i + 1] / 255) * da;
    const db = (D[i + 2] / 255) * da;
    const or_ = dr + (carry[j] - dr) * r;
    const og  = dg + (carry[j + 1] - dg) * r;
    const ob  = db + (carry[j + 2] - db) * r;
    const oa  = da + (carry[j + 3] - da) * r;
    if (oa > 0) {
      D[i]     = Math.round((or_ / oa) * 255);
      D[i + 1] = Math.round((og / oa) * 255);
      D[i + 2] = Math.round((ob / oa) * 255);
    } else {
      D[i] = D[i + 1] = D[i + 2] = 0;
    }
    D[i + 3] = Math.round(oa * 255);
    carry[j]     += (or_ - carry[j]) * q;
    carry[j + 1] += (og  - carry[j + 1]) * q;
    carry[j + 2] += (ob  - carry[j + 2]) * q;
    carry[j + 3] += (oa  - carry[j + 3]) * q;
  }
}

/** Extend the stroke toward a new raw pointer position. */
function moveStroke(rx, ry, pressure) {
  // Streamline: stamp toward a point that chases the cursor, smoothing
  // hand jitter into confident curves.
  const nx = stroke.x + (rx - stroke.x) * STREAMLINE;
  const ny = stroke.y + (ry - stroke.y) * STREAMLINE;
  // Travel direction, for tips that align to the stroke (bristle). Skip
  // near-zero movements — atan2 of jitter would make the tip flail.
  if (Math.hypot(nx - stroke.x, ny - stroke.y) > 0.5) {
    stroke.angle = Math.atan2(ny - stroke.y, nx - stroke.x);
  }
  const { stamps, rem } = stampPositions(
    stroke.x, stroke.y, nx, ny, stroke.pressure, pressure, state.brushSize, stroke.rem,
    stroke.smudge ? SMUDGE_SPACING : STAMP_SPACING);
  stroke.seg = null;
  for (const [x, y, p] of stamps) stamp(x, y, p);
  stroke.rem = rem;
  stroke.x = nx;
  stroke.y = ny;
  stroke.pressure = pressure;
  refreshStroke();
}

/** Re-merge plane+buffer into the preview over this event's dirty rect,
 *  patch the frame composite from it, and repaint. Smudge strokes mutate
 *  the preview directly in smudgeStamp — merging plane+buffer over their
 *  rect would wipe the smear, so they only patch and repaint. */
function refreshStroke() {
  const r = clampRect(stroke.seg);
  if (!r) { render(); return; }
  if (!stroke.smudge) {
    const g = stroke.prevCtx;
    g.save();
    g.beginPath();
    g.rect(r.x, r.y, r.w, r.h);
    g.clip();
    g.clearRect(r.x, r.y, r.w, r.h);
    g.drawImage(stroke.plane.canvas, 0, 0);
    g.globalAlpha = stroke.opacity;
    g.globalCompositeOperation = stroke.erase ? 'destination-out'
      : stroke.lock ? 'source-atop' : 'source-over';
    g.drawImage(stroke.buf, 0, 0);
    g.restore();
  }
  patchComposite(stroke.frame, r, stroke.preview);
  render();
}

/** Rebuild one rect of a frame's composite canvas. While a stroke is live,
 *  `override` (its preview canvas) stands in for the active plane. */
function patchComposite(f, r, override) {
  f.ctx.save();
  f.ctx.beginPath();
  f.ctx.rect(r.x, r.y, r.w, r.h);
  f.ctx.clip();
  f.ctx.clearRect(r.x, r.y, r.w, r.h);
  state.layers.forEach((m, li) => {
    if (!m.visible) return;
    const src = override && li === state.layer ? override : f.layers[li].canvas;
    f.ctx.globalAlpha = m.opacity;
    f.ctx.globalCompositeOperation = blendOp(m);
    f.ctx.drawImage(src, 0, 0);
  });
  f.ctx.restore(); // also resets globalAlpha / composite op
  f.ghost = null;
}

/** Merge the finished stroke into its plane and record undo history. */
function finishStroke() {
  const s = stroke;
  stroke = null;
  const r = clampRect(s.rect);
  if (!r) { render(); return; } // never touched the canvas
  const before = s.plane.ctx.getImageData(r.x, r.y, r.w, r.h);
  const after = s.prevCtx.getImageData(r.x, r.y, r.w, r.h);
  // Smudge drags alpha around as freely as color; on an alpha-locked layer
  // splice the original coverage back in (paint strokes get the same
  // guarantee from their source-atop merge, smudge has no merge step).
  if (s.smudge && s.lock) {
    for (let i = 3; i < after.data.length; i += 4) after.data[i] = before.data[i];
  }
  s.plane.ctx.putImageData(after, r.x, r.y);
  s.plane.touched = true;
  pushFreeUndo({ frame: s.frame, plane: s.plane, rect: r, before, after });
  patchComposite(s.frame, r); // re-read the real plane (drops the preview)
  updateThumb(s.frame);
  drawLayerThumb(state.layer);
  updateUI();
  render();
}

/* ======================================================================
 * Selection: lift / move / transform / clipboard / commit
 * ==================================================================== */

/** Show or hide the selection action bar. Call whenever selection/floating change. */
function syncSelectBar() {
  $('select-bar').hidden = !(selection || floating);
  updateSelReadout();
}

/**
 * Push the transform box's numbers into the select-bar's W/H/∠ fields — the
 * live readout while dragging, and the echo after typing. A field the user
 * is focused in is never overwritten (the readout must not fight the caret).
 */
function updateSelReadout() {
  const box = floating || selection;
  if (!box) return;
  const round1 = (v) => Math.round(v * 10) / 10;
  const put = (id, v) => {
    const el = $(id);
    if (document.activeElement !== el) el.value = v;
  };
  put('inp-sel-w', round1(box.w));
  put('inp-sel-h', round1(box.h));
  let deg = (((box.angle || 0) * 180) / Math.PI) % 360;
  if (deg > 180) deg -= 360;
  if (deg <= -180) deg += 360;
  put('inp-sel-angle', round1(deg));
}

/** Typed W/H/∠: lift if needed, then set the value exactly. Sizes resize
 *  about the box CENTER (typing a number shouldn't shove the art around);
 *  the angle is taken in degrees. Freeform only — the fields are hidden in
 *  pixel mode, whose selections deliberately never resample. */
function applyTypedTransform(field, raw) {
  if (state.mode !== 'free' || !liftSelection()) return;
  const f = floating;
  const v = parseFloat(raw);
  if (Number.isFinite(v)) {
    if (field === 'angle') {
      f.angle = (v * Math.PI) / 180;
    } else {
      const nv = clamp(v, 1, 100000);
      if (field === 'w') { f.x -= (nv - f.w) / 2; f.w = nv; }
      else { f.y -= (nv - f.h) / 2; f.h = nv; }
    }
  }
  render();
  updateSelReadout(); // echo the normalized value back into the fields
}
for (const [id, field] of [['inp-sel-w', 'w'], ['inp-sel-h', 'h'], ['inp-sel-angle', 'angle']]) {
  $(id).addEventListener('change', (e) => {
    e.target.blur(); // so the echo lands, and keyboard shortcuts come back
    applyTypedTransform(field, e.target.value);
  });
}

/** Paint a hex pixel array onto a fresh canvas (pixel-mode buffers). */
function hexToCanvas(pixels, w, h) {
  const c = document.createElement('canvas');
  c.width = w;
  c.height = h;
  const g = c.getContext('2d');
  const img = g.createImageData(w, h);
  const d = img.data;
  for (let i = 0; i < pixels.length; i++) {
    const col = pixels[i];
    if (!col) continue;
    const rgb = hexToRGB(col);
    const o = i * 4;
    d[o] = rgb[0]; d[o + 1] = rgb[1]; d[o + 2] = rgb[2]; d[o + 3] = 255;
  }
  g.putImageData(img, 0, 0);
  return c;
}

/** Rebuild the (pixel-mode) floating buffer's display canvas from its pixels. */
function rebuildFloatCanvas() {
  floating.canvas = hexToCanvas(floating.pixels, floating.w, floating.h);
}

/* --- Freeform transform-box geometry (pure — unit-tested via __ssmTest) ---
 * The box is {x, y, w, h, angle}: an axis-aligned rect rotated by `angle`
 * about its center. All math happens in art coordinates; the pointer side
 * converts through screenToArtF so zoom never enters these functions. */

/** Rotate (x, y) by `ang` radians about the origin. */
function rotVec(x, y, ang) {
  const c = Math.cos(ang), s = Math.sin(ang);
  return { x: x * c - y * s, y: x * s + y * c };
}

/** A box's corner/edge handles and rotate knob, in art coords. `hx`/`hy` are
 *  the handle's unit offsets from the center (corners ±1/±1, edges one zero).
 *  The knob floats `knobGap` art px beyond the top edge, following rotation. */
function boxHandles(box, knobGap) {
  const cx = box.x + box.w / 2, cy = box.y + box.h / 2;
  const ang = box.angle || 0;
  const at = (hx, hy, ex = 0) => {
    const v = rotVec(hx * box.w / 2, hy * box.h / 2 + ex, ang);
    return { hx, hy, x: cx + v.x, y: cy + v.y };
  };
  const list = [];
  for (const hy of [-1, 0, 1]) {
    for (const hx of [-1, 0, 1]) {
      if (hx || hy) list.push(at(hx, hy));
    }
  }
  list.push({ ...at(0, -1, -knobGap), rot: true });
  return list;
}

/** Is the (fractional art) point inside the rotated box? Un-rotates the
 *  point about the center and compares against the plain rect. */
function pointInBox(px, py, box) {
  const cx = box.x + box.w / 2, cy = box.y + box.h / 2;
  const v = rotVec(px - cx, py - cy, -(box.angle || 0));
  return Math.abs(v.x) <= box.w / 2 && Math.abs(v.y) <= box.h / 2;
}

/** Axis-aligned bounds of the rotated box, grown by 1px for the soft edge
 *  antialiased commits produce. Returns {x0, y0, x1, y1} for clampRect. */
function boxBounds(box) {
  const cx = box.x + box.w / 2, cy = box.y + box.h / 2;
  const ang = box.angle || 0;
  // Rotation maps the half-extents onto both axes by |cos| and |sin|.
  const ex = (Math.abs(Math.cos(ang)) * box.w + Math.abs(Math.sin(ang)) * box.h) / 2;
  const ey = (Math.abs(Math.sin(ang)) * box.w + Math.abs(Math.cos(ang)) * box.h) / 2;
  // cos(π/2) is 6e-17, not 0 — snap near-integers before floor/ceil so exact
  // quarter turns don't book a needlessly fatter patch.
  const snap = (v) => (Math.abs(v - Math.round(v)) < 1e-9 ? Math.round(v) : v);
  return {
    x0: Math.floor(snap(cx - ex)) - 1, y0: Math.floor(snap(cy - ey)) - 1,
    x1: Math.ceil(snap(cx + ex)) + 1, y1: Math.ceil(snap(cy + ey)) + 1,
  };
}

/**
 * Resize the box by dragging handle (hx, hy) to the pointer (px, py), the
 * OPPOSITE handle staying anchored in art space — corners stretch both axes
 * (`uniform` locks aspect, for Shift), edge handles stretch one. Returns the
 * new {x, y, w, h}; angle is unchanged. Pure: computes from the drag-start
 * box each move, so the resize never accumulates rounding.
 */
function scaleBox(box, hx, hy, px, py, uniform) {
  const ang = box.angle || 0;
  const cx = box.x + box.w / 2, cy = box.y + box.h / 2;
  const a = rotVec(-hx * box.w / 2, -hy * box.h / 2, ang); // anchor (opposite pt)
  const ax = cx + a.x, ay = cy + a.y;
  // Pointer in the box's own (un-rotated) frame, relative to the anchor.
  const local = rotVec(px - ax, py - ay, -ang);
  let w = box.w, h = box.h;
  if (uniform && hx && hy) {
    // Corner + Shift: one scale factor for both axes — the larger of the two
    // pulls so the content always tracks the cursor's dominant direction.
    const s = Math.max(local.x * hx / box.w, local.y * hy / box.h, 1 / Math.min(box.w, box.h));
    w = box.w * s;
    h = box.h * s;
  } else {
    if (hx) w = Math.max(1, local.x * hx); // projection onto the drag axis;
    if (hy) h = Math.max(1, local.y * hy); // dragging past the anchor clamps
  }
  // Re-derive the center from the fixed anchor and the new half-extents.
  const c = rotVec(hx ? hx * w / 2 : 0, hy ? hy * h / 2 : 0, ang);
  return { x: ax + c.x - w / 2, y: ay + c.y - h / 2, w, h };
}

/** Handle under the screen point, or null. Checks the knob first (it can sit
 *  near the n handle at small sizes); ~9 screen px of grab slack. */
function hitHandle(sx, sy, box) {
  const R = 9;
  const list = boxHandles(box, KNOB_GAP / state.zoom);
  list.reverse(); // knob (pushed last) wins ties
  for (const hnd of list) {
    const hx = state.panX + hnd.x * state.zoom;
    const hy = state.panY + hnd.y * state.zoom;
    if (Math.hypot(sx - hx, sy - hy) <= R) return hnd;
  }
  return null;
}

const KNOB_GAP = 26; // screen px between the top edge and the rotate knob

/** CSS cursor for a resize handle: the handle's on-screen direction (box
 *  rotation included) bucketed into the four resize arrows — opposite
 *  handles share one, so the modulo folds 360° down to 180°. */
const RESIZE_CURSORS = ['ew-resize', 'nwse-resize', 'ns-resize', 'nesw-resize'];
function resizeCursor(hnd, ang) {
  const v = rotVec(hnd.hx, hnd.hy, ang);
  let deg = (Math.atan2(v.y, v.x) * 180) / Math.PI; // screen y points down
  deg = ((deg % 180) + 180) % 180;
  return RESIZE_CURSORS[Math.round(deg / 45) % 4];
}

/**
 * Lift the selected pixels off the active layer into the floating buffer.
 * The layer keeps a hole where they were; `liftEntry` remembers the undo
 * snapshot so cancel can restore it and commit can merge with it (one undo
 * step reverts a whole move). Returns false if there's nothing to lift.
 */
function liftSelection() {
  if (floating || !selection) return !!floating;
  if (!state.layers[state.layer].visible) {
    flashHint('The active layer is hidden — click its eye to show it first.');
    return false;
  }
  const { x, y, w, h } = selection;

  // Freeform: cut the region's RGBA out into a floating canvas. No history
  // entry yet — commit/cancel/discard reconstruct the "before" state from
  // liftBefore, so a whole move is always exactly one undo step.
  if (state.mode === 'free') {
    const plane = curLayer();
    const liftBefore = plane.ctx.getImageData(x, y, w, h);
    const c = document.createElement('canvas');
    c.width = w;
    c.height = h;
    c.getContext('2d').putImageData(liftBefore, 0, 0);
    plane.ctx.clearRect(x, y, w, h);
    plane.touched = true;
    floating = {
      pixels: null, w, h, x, y, canvas: c,
      angle: 0, sw: w, sh: h, // transform box starts identity; sw/sh = the
                              // canvas's natural size, fixed for its lifetime
      liftRect: { x, y, w, h }, liftBefore, liftEntry: null,
    };
    patchComposite(cur(), { x, y, w, h });
    updateThumb(cur());
    drawLayerThumb(state.layer);
    return true;
  }

  pushUndo();
  const entry = state.undo[state.undo.length - 1];
  const plane = curLayer();
  const buf = new Array(w * h).fill(null);
  batchPixels(() => {
    for (let dy = 0; dy < h; dy++) {
      for (let dx = 0; dx < w; dx++) {
        const c = plane.pixels[idx(x + dx, y + dy)];
        if (c) {
          buf[dy * w + dx] = c;
          setPixel(x + dx, y + dy, null, true); // lifts bypass alpha lock
        }
      }
    }
  });
  floating = { pixels: buf, w, h, x, y, canvas: null, liftEntry: entry };
  rebuildFloatCanvas();
  updateThumb(cur());
  drawLayerThumb(state.layer);
  updateUI();
  return true;
}

/**
 * Stamp the floating buffer onto the active layer at its current position
 * (out-of-bounds pixels just clip away). If the buffer was lifted and the
 * lift is still the newest undo entry, no second snapshot is taken — so one
 * Ctrl+Z reverts the whole lift-move-commit.
 */
function commitFloat() {
  if (!floating) return;
  const f = floating;
  floating = null;

  // Freeform: stamp the buffer (source-over, so its transparent parts keep
  // the art below) and record ONE patch covering both the lift hole and the
  // landing area — before = the plane as it was before the lift.
  //
  // The landing itself has three quality tiers, because the transform box
  // may have been rotated/resized since the lift:
  //  1. identity at integer coords — plain drawImage, byte-exact (a move
  //     never costs quality, exactly as before free transform existed);
  //  2. quarter turn at natural size — bake the rotation on the pixel grid
  //     first (every pixel maps to a pixel; the buttons produce this case),
  //     rounding the landing spot ≤½px: still zero resampling;
  //  3. anything else — ONE smoothed drawImage through the full transform
  //     (the source canvas was never touched while editing, so however long
  //     the user fiddled, the content resamples exactly once).
  if (state.mode === 'free') {
    const plane = curLayer();
    const frame = cur();
    const TAU = Math.PI * 2;
    const ang = ((f.angle % TAU) + TAU) % TAU;
    const quarter = Math.round(ang / (Math.PI / 2)) % 4;
    const onQuarter = Math.abs(ang - Math.round(ang / (Math.PI / 2)) * (Math.PI / 2)) < 1e-6;
    const natural = Math.abs(f.w - f.sw) < 1e-6 && Math.abs(f.h - f.sh) < 1e-6;
    const whole = (v) => Math.abs(v - Math.round(v)) < 1e-6;

    let land = null; // {canvas, x, y} when the landing needs no resampling
    if (onQuarter && natural) {
      let c = f.canvas;
      if (quarter) {
        c = document.createElement('canvas');
        c.width = quarter % 2 ? f.sh : f.sw;
        c.height = quarter % 2 ? f.sw : f.sh;
        const g = c.getContext('2d');
        g.translate(c.width / 2, c.height / 2);
        g.rotate(quarter * (Math.PI / 2));
        g.drawImage(f.canvas, -f.sw / 2, -f.sh / 2);
      }
      const lx = f.x + f.w / 2 - c.width / 2;
      const ly = f.y + f.h / 2 - c.height / 2;
      // An unrotated buffer at a fractional spot (possible after resizing
      // back to natural size) must NOT snap — the user placed it there.
      if (quarter || (whole(lx) && whole(ly))) {
        land = { canvas: c, x: Math.round(lx), y: Math.round(ly) };
      }
    }
    const placeRect = clampRect(land
      ? { x0: land.x, y0: land.y, x1: land.x + land.canvas.width, y1: land.y + land.canvas.height }
      : boxBounds(f));
    let u = null;
    if (f.liftRect) {
      u = growRect(u, f.liftRect.x, f.liftRect.y,
                   f.liftRect.x + f.liftRect.w, f.liftRect.y + f.liftRect.h);
    }
    if (placeRect) {
      u = growRect(u, placeRect.x, placeRect.y,
                   placeRect.x + placeRect.w, placeRect.y + placeRect.h);
    }
    const r = clampRect(u);
    if (r) {
      const beforeC = document.createElement('canvas');
      beforeC.width = r.w;
      beforeC.height = r.h;
      const bg = beforeC.getContext('2d');
      bg.putImageData(plane.ctx.getImageData(r.x, r.y, r.w, r.h), 0, 0);
      if (f.liftBefore) {
        bg.putImageData(f.liftBefore, f.liftRect.x - r.x, f.liftRect.y - r.y);
      }
      const before = bg.getImageData(0, 0, r.w, r.h);
      if (land) {
        plane.ctx.drawImage(land.canvas, land.x, land.y);
      } else {
        plane.ctx.save();
        plane.ctx.imageSmoothingEnabled = true;
        plane.ctx.translate(f.x + f.w / 2, f.y + f.h / 2);
        plane.ctx.rotate(f.angle);
        plane.ctx.scale(f.w / f.sw, f.h / f.sh);
        plane.ctx.drawImage(f.canvas, -f.sw / 2, -f.sh / 2);
        plane.ctx.restore();
      }
      plane.touched = true;
      const after = plane.ctx.getImageData(r.x, r.y, r.w, r.h);
      pushFreeUndo({ frame, plane, rect: r, before, after });
      patchComposite(frame, r);
    }
    selection = placeRect; // keep the landed (clipped) area selected
    updateThumb(frame);
    drawLayerThumb(state.layer);
    updateUI();
    syncSelectBar();
    render();
    return;
  }

  if (!(f.liftEntry && state.undo[state.undo.length - 1] === f.liftEntry)) pushUndo();
  batchPixels(() => {
    for (let dy = 0; dy < f.h; dy++) {
      for (let dx = 0; dx < f.w; dx++) {
        const c = f.pixels[dy * f.w + dx];
        if (c) setPixel(f.x + dx, f.y + dy, c, true); // placing bypasses alpha lock
      }
    }
  });
  // Keep the (canvas-clipped) area selected so it can be grabbed again.
  const x0 = Math.max(0, f.x), y0 = Math.max(0, f.y);
  const x1 = Math.min(state.width, f.x + f.w), y1 = Math.min(state.height, f.y + f.h);
  selection = x1 > x0 && y1 > y0 ? { x: x0, y: y0, w: x1 - x0, h: y1 - y0 } : null;
  updateThumb(cur());
  drawLayerThumb(state.layer);
  updateUI();
  syncSelectBar();
  render();
}

/** Esc / ✕ / right-click: put lifted pixels back where they came from (and
 *  drop the lift's undo entry — net zero); a pasted buffer is just discarded. */
function cancelSelection() {
  if (floating && state.mode === 'free') {
    if (floating.liftBefore) {
      // Pour the lifted RGBA back into its hole — net zero, no history.
      const plane = curLayer();
      plane.ctx.putImageData(floating.liftBefore, floating.liftRect.x, floating.liftRect.y);
      patchComposite(cur(), floating.liftRect);
      updateThumb(cur());
      refreshLayerThumbs();
    }
    floating = null; // a pasted buffer is simply discarded
  } else if (floating) {
    const entry = floating.liftEntry;
    if (entry && state.undo[state.undo.length - 1] === entry) {
      state.undo.pop();
      entry.plane.pixels = entry.pixels;
      repaintLayer(entry.plane);
      recomposite(entry.frame);
      updateThumb(entry.frame);
      refreshLayerThumbs();
    }
    floating = null;
  }
  selection = null;
  updateUI();
  syncSelectBar();
  render();
}

/** Lift if needed, then remap the buffer's pixels. 90°-step rotations and
 *  flips are exact on a pixel grid — pure index shuffles, no resampling. */
function transformFloat(fn) {
  if (!liftSelection()) return;
  fn(floating);
  rebuildFloatCanvas();
  syncSelectBar();
  render();
}

function rotateFloat(cw) {
  // Freeform: the buttons are just ±90° on the transform box's live angle —
  // no bake, no quality cost (commit detects quarter turns at natural size
  // and lands them through the exact grid-aligned path).
  if (state.mode === 'free') {
    if (!liftSelection()) return;
    floating.angle += ((cw ? 90 : -90) * Math.PI) / 180;
    syncSelectBar();
    render();
    return;
  }
  transformFloat((f) => {
    const { w, h, pixels } = f;
    const out = new Array(w * h).fill(null);
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const nx = cw ? h - 1 - y : y;
        const ny = cw ? x : w - 1 - x;
        out[ny * h + nx] = pixels[y * w + x]; // new row width = h
      }
    }
    f.pixels = out;
    f.w = h;
    f.h = w;
    // Keep the buffer centered on the same spot as its dimensions swap.
    f.x += Math.floor((w - h) / 2);
    f.y += Math.floor((h - w) / 2);
  });
}

function flipFloat(horizontal) {
  // Freeform: bake the mirror into the source canvas (an axis mirror is
  // exact — every pixel maps to a pixel) and negate the angle, because the
  // on-screen mirror of a +20°-tilted box is that content tilted −20°.
  if (state.mode === 'free') {
    if (!liftSelection()) return;
    const f = floating;
    const c = document.createElement('canvas');
    c.width = f.sw;
    c.height = f.sh;
    const g = c.getContext('2d');
    g.translate(horizontal ? f.sw : 0, horizontal ? 0 : f.sh);
    g.scale(horizontal ? -1 : 1, horizontal ? 1 : -1);
    g.drawImage(f.canvas, 0, 0);
    f.canvas = c;
    f.angle = -f.angle;
    syncSelectBar();
    render();
    return;
  }
  transformFloat((f) => {
    const { w, h, pixels } = f;
    const out = new Array(w * h);
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        out[horizontal ? y * w + (w - 1 - x) : (h - 1 - y) * w + x] = pixels[y * w + x];
      }
    }
    f.pixels = out;
  });
}

/** Copy the selection (or the floating buffer) to the app clipboard.
 *  Pixel content is stored as a hex array, freeform as an RGBA canvas —
 *  paste converts between them, so the clipboard works across modes. */
function copySelection() {
  const snap = (src, w, h, sx, sy) => { // copy a canvas region to a fresh canvas
    const c = document.createElement('canvas');
    c.width = w;
    c.height = h;
    c.getContext('2d').drawImage(src, -sx, -sy);
    return c;
  };
  if (floating) {
    if (state.mode === 'free') {
      const f = floating;
      if (f.angle || f.w !== f.sw || f.h !== f.sh) {
        // Transformed: copy what's on screen — bake the rotation/scale into
        // a bounds-sized canvas (the float itself keeps its pristine source).
        const b = boxBounds(f);
        const c = document.createElement('canvas');
        c.width = b.x1 - b.x0;
        c.height = b.y1 - b.y0;
        const g = c.getContext('2d');
        g.translate(f.x + f.w / 2 - b.x0, f.y + f.h / 2 - b.y0);
        g.rotate(f.angle);
        g.scale(f.w / f.sw, f.h / f.sh);
        g.drawImage(f.canvas, -f.sw / 2, -f.sh / 2);
        clipboard = { canvas: c, w: c.width, h: c.height };
      } else {
        clipboard = { canvas: snap(f.canvas, f.sw, f.sh, 0, 0), w: f.sw, h: f.sh };
      }
    } else {
      clipboard = { pixels: floating.pixels.slice(), w: floating.w, h: floating.h };
    }
  } else if (selection) {
    const { x, y, w, h } = selection;
    const plane = curLayer();
    if (state.mode === 'free') {
      clipboard = { canvas: snap(plane.canvas, w, h, x, y), w, h };
    } else {
      const buf = new Array(w * h).fill(null);
      for (let dy = 0; dy < h; dy++) {
        for (let dx = 0; dx < w; dx++) {
          buf[dy * w + dx] = plane.pixels[idx(x + dx, y + dy)];
        }
      }
      clipboard = { pixels: buf, w, h };
    }
  } else {
    return;
  }
  flashHint('Copied — Ctrl+V pastes, on any frame or layer.');
}

/** Drop the floating buffer, keeping its lift hole as a deletion. In pixel
 *  mode the lift's undo entry already covers that; freeform lifts don't make
 *  one (see liftSelection), so record the hole as a patch here. */
function discardFloat() {
  if (state.mode === 'free' && floating.liftRect) {
    const { liftRect: r, liftBefore } = floating;
    const plane = curLayer();
    const after = plane.ctx.getImageData(r.x, r.y, r.w, r.h);
    pushFreeUndo({ frame: cur(), plane, rect: r, before: liftBefore, after });
    updateUI();
  }
  floating = null;
}

/** Cut = copy + remove. A lifted buffer's hole is already the removal. */
function cutSelection() {
  if (!selection && !floating) return;
  if (floating) {
    copySelection();
    discardFloat();
    selection = null;
    syncSelectBar();
    render();
    return;
  }
  copySelection();
  clearSelectionPixels();
}

/** Delete/Clear: erase the selected area (or discard the floating buffer). */
function clearSelectionPixels() {
  if (floating) {
    discardFloat();
    syncSelectBar();
    render();
    return;
  }
  if (!selection) return;
  if (!state.layers[state.layer].visible) {
    flashHint('The active layer is hidden — click its eye to show it first.');
    return;
  }
  if (state.mode === 'free') {
    const { x, y, w, h } = selection;
    const plane = curLayer();
    const before = plane.ctx.getImageData(x, y, w, h);
    plane.ctx.clearRect(x, y, w, h);
    plane.touched = true;
    const after = plane.ctx.getImageData(x, y, w, h);
    pushFreeUndo({ frame: cur(), plane, rect: { x, y, w, h }, before, after });
    patchComposite(cur(), { x, y, w, h });
  } else {
    pushUndo();
    batchPixels(() => {
      for (let dy = 0; dy < selection.h; dy++) {
        for (let dx = 0; dx < selection.w; dx++) {
          setPixel(selection.x + dx, selection.y + dy, null, true); // Del bypasses alpha lock
        }
      }
    });
  }
  updateThumb(cur());
  drawLayerThumb(state.layer);
  updateUI();
  render();
}

/** The clipboard's content as an RGBA canvas (for pasting into freeform). */
function clipboardCanvas() {
  if (clipboard.pixels) return hexToCanvas(clipboard.pixels, clipboard.w, clipboard.h);
  const c = document.createElement('canvas'); // snapshot, so transforms
  c.width = clipboard.w;                      // never touch the clipboard
  c.height = clipboard.h;
  c.getContext('2d').drawImage(clipboard.canvas, 0, 0);
  return c;
}

/** The clipboard's content as a hex pixel array (for pasting into pixel
 *  mode). Freeform content flattens the way PNG import does: alpha < 128
 *  becomes transparent, the rest opaque. */
function clipboardPixels() {
  if (clipboard.pixels) return clipboard.pixels.slice();
  const d = clipboard.canvas.getContext('2d')
    .getImageData(0, 0, clipboard.w, clipboard.h).data;
  const toHex = (v) => v.toString(16).padStart(2, '0');
  const out = new Array(clipboard.w * clipboard.h).fill(null);
  for (let i = 0; i < out.length; i++) {
    const o = i * 4;
    if (d[o + 3] >= 128) out[i] = `#${toHex(d[o])}${toHex(d[o + 1])}${toHex(d[o + 2])}`;
  }
  return out;
}

/** Paste the clipboard as a floating buffer, centered in the viewport. */
function pasteClipboard() {
  if (!clipboard) {
    flashHint('Nothing copied yet — select an area and Ctrl+C first.');
    return;
  }
  if (!state.layers[state.layer].visible) {
    flashHint('The active layer is hidden — click its eye to show it first.');
    return;
  }
  commitFloat();
  selectTool('select');
  const cx = Math.round((viewW / 2 - state.panX) / state.zoom - clipboard.w / 2);
  const cy = Math.round((viewH / 2 - state.panY) / state.zoom - clipboard.h / 2);
  floating = {
    pixels: state.mode === 'free' ? null : clipboardPixels(),
    w: clipboard.w,
    h: clipboard.h,
    x: clamp(cx, 1 - clipboard.w, state.width - 1),
    y: clamp(cy, 1 - clipboard.h, state.height - 1),
    canvas: state.mode === 'free' ? clipboardCanvas() : null,
    angle: 0,
    sw: clipboard.w,
    sh: clipboard.h,
    liftRect: null,
    liftBefore: null,
    liftEntry: null,
  };
  if (state.mode === 'pixel') rebuildFloatCanvas();
  syncSelectBar();
  render();
}

/** Arrow keys: nudge the selection contents by whole pixels (lifting first). */
function nudgeSelection(dx, dy) {
  if (!selection && !floating) return false;
  if (!liftSelection()) return false;
  floating.x += dx;
  floating.y += dy;
  render();
  return true;
}

$('btn-sel-rotl').addEventListener('click', () => rotateFloat(false));
$('btn-sel-rotr').addEventListener('click', () => rotateFloat(true));
$('btn-sel-fliph').addEventListener('click', () => flipFloat(true));
$('btn-sel-flipv').addEventListener('click', () => flipFloat(false));
$('btn-sel-copy').addEventListener('click', copySelection);
$('btn-sel-cut').addEventListener('click', cutSelection);
$('btn-sel-del').addEventListener('click', clearSelectionPixels);
$('btn-sel-commit').addEventListener('click', commitFloat);
$('btn-sel-cancel').addEventListener('click', cancelSelection);

/* ======================================================================
 * Pointer input (mouse / pen / touch via Pointer Events)
 * ==================================================================== */

view.addEventListener('pointerdown', (e) => {
  const sx = e.offsetX, sy = e.offsetY;

  // Middle button, the pan tool, or left button while holding space: pan.
  if (e.button === 1 || (e.button === 0 && (spaceDown || state.tool === 'pan'))) {
    panning = true;
    panAnchor = { sx, sy, panX: state.panX, panY: state.panY };
    view.style.cursor = ''; // the transform hover cursor must not mask the pan grab
    wrap.classList.add('panning-active');
    view.setPointerCapture(e.pointerId);
    e.preventDefault();
    return;
  }

  if (e.button !== 0 && e.button !== 2) return;

  // Playback: any click on the canvas pauses AND lands on the frame that
  // was showing — watch the loop, see the frame that's wrong, click, fix.
  // (Panning above stays live; the Pause button instead returns to the
  // frame that was being edited, because playback never moves it.)
  if (playing) {
    selectFrame(playFrame); // pauses via selectFrame's playback guard
    return; // the click is spent on landing; the next one edits
  }

  const p = screenToArt(sx, sy);
  const rightBtn = e.button === 2;

  // Alt+click is a temporary eyedropper regardless of the active tool.
  if (e.altKey || state.tool === 'eyedropper') {
    eyedrop(p.x, p.y);
    return;
  }

  if (state.tool === 'select') {
    if (rightBtn) {
      cancelSelection();
      return;
    }
    // Freeform: transform-handle grabs beat everything else. The handles
    // live on the plain marquee too — grabbing one lifts first, so "select,
    // then immediately rotate/resize" is one gesture.
    if (state.mode === 'free' && (floating || selection)) {
      const hnd = hitHandle(sx, sy, floating || selection);
      if (hnd && liftSelection()) {
        const f = floating;
        const q = screenToArtF(sx, sy);
        const fcx = f.x + f.w / 2, fcy = f.y + f.h / 2;
        xformDrag = hnd.rot
          ? { kind: 'rotate', cx: fcx, cy: fcy, start: f.angle,
              grab: Math.atan2(q.y - fcy, q.x - fcx) }
          // Scaling recomputes from this drag-start box every move, so a
          // long wiggly drag can't accumulate rounding into the size.
          : { kind: 'scale', hx: hnd.hx, hy: hnd.hy,
              box: { x: f.x, y: f.y, w: f.w, h: f.h, angle: f.angle } };
        if (hnd.rot) view.style.cursor = 'grabbing'; // the knob is held now
        view.setPointerCapture(e.pointerId);
        render();
        return;
      }
    }
    const q = screenToArtF(sx, sy);
    const inside = (r) => r && (state.mode === 'free'
      ? pointInBox(q.x, q.y, r)
      : p.x >= r.x && p.x < r.x + r.w && p.y >= r.y && p.y < r.y + r.h);
    if (floating) {
      if (inside(floating)) {
        floatDrag = { dx: p.x - floating.x, dy: p.y - floating.y };
        view.setPointerCapture(e.pointerId);
      } else {
        commitFloat(); // click outside stamps it down
      }
      return;
    }
    if (inside(selection)) {
      // Grab the selection contents: lift, then drag.
      if (liftSelection()) {
        floatDrag = { dx: p.x - floating.x, dy: p.y - floating.y };
        view.setPointerCapture(e.pointerId);
        render();
      }
      return;
    }
    // Start a fresh marquee.
    const ax = clamp(p.x, 0, state.width - 1);
    const ay = clamp(p.y, 0, state.height - 1);
    selDrag = { x0: ax, y0: ay };
    selection = { x: ax, y: ay, w: 1, h: 1 };
    view.setPointerCapture(e.pointerId);
    syncSelectBar();
    render();
    return;
  }

  // Drawing on a layer you can't see only causes confusion — block it.
  if (!state.layers[state.layer].visible) {
    flashHint('The active layer is hidden — click its eye to show it first.');
    return;
  }

  // Erasing only ever removes alpha, which alpha lock forbids — refuse the
  // stroke up front (both modes) rather than let it silently do nothing.
  // Fill is excluded: the fill paths carry their own more specific hints.
  if (state.layers[state.layer].alphaLock && state.tool !== 'fill' &&
      (rightBtn || state.tool === 'eraser')) {
    flashHint('Layer alpha is locked — unlock it to erase.');
    return;
  }

  // Freeform painting & filling (select was handled above, both modes).
  if (state.mode === 'free') {
    if (state.tool === 'fill') {
      freeFill(p.x, p.y, rightBtn ? null : state.color);
      if (!rightBtn) addUsedColor(state.color);
      return;
    }
    const q = screenToArtF(sx, sy);
    const erase = rightBtn || state.tool === 'eraser';
    // Right-drag stays the eraser even on the smudge tool.
    beginStroke(q.x, q.y, penPressure(e), erase, state.tool === 'smudge' && !rightBtn);
    if (!erase && state.tool !== 'smudge') addUsedColor(state.color);
    view.setPointerCapture(e.pointerId);
    return;
  }

  if (state.tool === 'fill') {
    strokeChanged = false;
    pushUndo();
    floodFill(p.x, p.y, rightBtn ? null : state.color);
    popUndoIfUnchanged();
    if (strokeChanged) {
      updateThumb(cur());
      drawLayerThumb(state.layer);
    }
    if (!rightBtn) addUsedColor(state.color);
    updateUI();
    render();
    return;
  }

  // Brush / eraser stroke. Right-drag always erases, whatever the tool.
  drawing = true;
  erasing = rightBtn || state.tool === 'eraser';
  strokeChanged = false;
  pushUndo();
  lastArt = p;
  paintStamp(p.x, p.y, erasing ? null : state.color);
  if (!erasing) addUsedColor(state.color);
  view.setPointerCapture(e.pointerId);
  render();
});

view.addEventListener('pointermove', (e) => {
  const sx = e.offsetX, sy = e.offsetY;
  hoverS = { x: sx, y: sy }; // raw screen position (freeform brush circle)

  if (panning) {
    state.panX = panAnchor.panX + (sx - panAnchor.sx);
    state.panY = panAnchor.panY + (sy - panAnchor.sy);
    render();
    return;
  }

  const p = screenToArt(sx, sy);
  hover = inBounds(p.x, p.y) ? p : null;

  if (selDrag) {
    // Grow the marquee between its anchor and the (clamped) cursor.
    const cx = clamp(p.x, 0, state.width - 1);
    const cy = clamp(p.y, 0, state.height - 1);
    selection = {
      x: Math.min(selDrag.x0, cx),
      y: Math.min(selDrag.y0, cy),
      w: Math.abs(cx - selDrag.x0) + 1,
      h: Math.abs(cy - selDrag.y0) + 1,
    };
    updateSelReadout(); // the W/H fields track the marquee as it grows
    updateStatus();
    render();
    return;
  }
  if (xformDrag && floating) {
    const q = screenToArtF(sx, sy);
    if (xformDrag.kind === 'rotate') {
      let a = xformDrag.start
            + Math.atan2(q.y - xformDrag.cy, q.x - xformDrag.cx) - xformDrag.grab;
      // Shift snaps to 15° steps — enough to hit 45/90 without a protractor.
      if (e.shiftKey) a = Math.round(a / (Math.PI / 12)) * (Math.PI / 12);
      floating.angle = a;
    } else {
      const b = scaleBox(xformDrag.box, xformDrag.hx, xformDrag.hy, q.x, q.y, e.shiftKey);
      floating.x = b.x;
      floating.y = b.y;
      floating.w = b.w;
      floating.h = b.h;
    }
    updateSelReadout(); // live W/H/∠ numbers while the handle drags
    updateStatus();
    render();
    return;
  }
  if (floatDrag) {
    floating.x = p.x - floatDrag.dx;
    floating.y = p.y - floatDrag.dy;
    updateStatus();
    render();
    return;
  }

  if (stroke) {
    const q = screenToArtF(sx, sy);
    moveStroke(q.x, q.y, penPressure(e)); // stamps, patches, renders
    updateStatus();
    return;
  }

  if (drawing) {
    // Connect from the last position so fast drags don't leave gaps.
    paintLine(lastArt.x, lastArt.y, p.x, p.y, erasing ? null : state.color);
    lastArt = p;
  }

  // Hover feedback for the freeform transform handles: track which one is
  // under the cursor so render() can light it up — nobody should have to
  // guess whether a click will grab the knob or land beside the box. The
  // mouse cursor tells the same story: directional resize arrows over the
  // handles (matching each handle's on-screen direction, rotation included),
  // grab over the knob, move inside the box. Inline style, so it must be
  // cleared whenever nothing transform-y is underneath (or the pan
  // override classes could never show through).
  const selBox = (state.mode === 'free' && state.tool === 'select' && (floating || selection))
    ? floating || selection
    : null;
  hoverHandle = selBox ? hitHandle(sx, sy, selBox) : null;
  if (selBox && !spaceDown) {
    const q = screenToArtF(sx, sy);
    view.style.cursor = hoverHandle
      ? (hoverHandle.rot ? 'grab' : resizeCursor(hoverHandle, selBox.angle || 0))
      : (pointInBox(q.x, q.y, selBox) ? 'move' : '');
  } else if (view.style.cursor) {
    view.style.cursor = '';
  }

  updateStatus();
  render();
});

function endStroke() {
  if (panning) {
    panning = false;
    wrap.classList.remove('panning-active');
  }
  selDrag = null;
  floatDrag = null;
  // Releasing the knob relaxes grabbing back to grab; the next pointermove
  // re-derives the cursor from whatever is actually underneath.
  if (xformDrag && xformDrag.kind === 'rotate') view.style.cursor = 'grab';
  xformDrag = null;
  if (stroke) {
    finishStroke(); // freeform stroke: merge + history
    return;
  }
  if (drawing) {
    drawing = false;
    popUndoIfUnchanged(); // don't pollute history with strokes that changed nothing
    if (strokeChanged) {
      updateThumb(cur());
      drawLayerThumb(state.layer);
    }
    updateUI();
  }
}

view.addEventListener('pointerup', endStroke);
view.addEventListener('pointercancel', endStroke);

view.addEventListener('pointerleave', () => {
  hover = null;
  hoverS = null;
  hoverHandle = null;
  updateStatus();
  if (!drawing && !stroke) render();
});

// Right-click is the eraser, so never show the browser context menu here.
view.addEventListener('contextmenu', (e) => e.preventDefault());

// Middle-click autoscroll would fight with middle-drag panning.
view.addEventListener('mousedown', (e) => {
  if (e.button === 1) e.preventDefault();
});

// Wheel = zoom, anchored on the cursor. passive:false lets us stop page scroll.
wrap.addEventListener('wheel', (e) => {
  e.preventDefault();
  const factor = e.deltaY < 0 ? 1.2 : 1 / 1.2;
  setZoom(state.zoom * factor, e.offsetX, e.offsetY);
}, { passive: false });

/* ======================================================================
 * Keyboard shortcuts
 * ==================================================================== */

window.addEventListener('keydown', (e) => {
  // Escape closes the File menu — checked before the input guard so it also
  // works while focus is in the menu's W/H fields.
  if (e.code === 'Escape' && !fileMenu.hidden) {
    fileMenu.hidden = true;
    return;
  }
  // Don't steal keystrokes from inputs, the animation textarea, or selects.
  if (e.target instanceof HTMLInputElement ||
      e.target instanceof HTMLTextAreaElement ||
      e.target instanceof HTMLSelectElement) return;

  if (e.code === 'Space') {
    spaceDown = true;
    wrap.classList.add('panning');
    e.preventDefault();
    return;
  }
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyZ') {
    e.preventDefault();
    if (e.shiftKey) redo(); else undo();
    return;
  }
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyY') {
    e.preventDefault();
    redo();
    return;
  }
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyS') {
    e.preventDefault(); // browsers' "save page" dialog would appear otherwise
    saveProject();
    return;
  }
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyC') {
    copySelection();
    return;
  }
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyX') {
    cutSelection();
    return;
  }
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyV') {
    pasteClipboard();
    return;
  }
  if (e.ctrlKey || e.metaKey || e.altKey) return;

  // Arrow keys nudge the selection contents (lifting them first).
  if (e.code.startsWith('Arrow') && (selection || floating)) {
    const d = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1] }[e.code];
    if (d && nudgeSelection(d[0], d[1])) {
      e.preventDefault();
      return;
    }
  }

  switch (e.code) {
    case 'KeyB': selectTool('brush'); break;
    case 'KeyE': selectTool('eraser'); break;
    case 'KeyU': selectTool('smudge'); break;           // freeform only (guarded)
    case 'KeyG': selectTool('fill'); break;
    case 'KeyI': selectTool('eyedropper'); break;
    case 'KeyH': selectTool('pan'); break;
    case 'KeyS': selectTool('select'); break;
    case 'Escape': cancelSelection(); break;
    case 'Enter': commitFloat(); break;
    case 'Comma': selectFrame(state.frame - 1); break;   // previous frame
    case 'Period': selectFrame(state.frame + 1); break;  // next frame
    case 'KeyN': addFrame(); break;
    case 'KeyD': dupFrame(); break;
    case 'Delete':
      // With a selection active, Delete clears it; otherwise it's the frame.
      if (selection || floating) clearSelectionPixels();
      else deleteFrame();
      break;
    case 'BracketLeft': setBrushSize(state.brushSize - 1); break;
    case 'BracketRight': setBrushSize(state.brushSize + 1); break;
    case 'KeyO': $('chk-onion-prev').click(); break;     // toggle prev ghost
    case 'KeyX': $('chk-origin').click(); break;         // toggle origin guides
    case 'KeyP': setPlaying(!playing); break;            // play / pause preview
    case 'Digit0': fitView(); break;
    case 'Equal': case 'NumpadAdd':
      setZoom(state.zoom * 1.2, viewW / 2, viewH / 2); break;
    case 'Minus': case 'NumpadSubtract':
      setZoom(state.zoom / 1.2, viewW / 2, viewH / 2); break;
  }
});

window.addEventListener('keyup', (e) => {
  if (e.code === 'Space') {
    spaceDown = false;
    wrap.classList.remove('panning');
  }
});

/* ======================================================================
 * Frame management & frame strip UI
 * ==================================================================== */

const THUMB = 52; // max thumbnail edge, px (fits the 60px strip buttons)

/** Switch which frame is being edited and re-highlight the strip. */
function selectFrame(i) {
  // Navigating to a specific frame ends playback: strip clicks, , / . ,
  // undo's jump-to-frame, and frame ops all funnel through here.
  if (playing) setPlaying(false);
  commitFloat(); // a floating selection belongs to the frame it was lifted from
  state.frame = clamp(i, 0, state.frames.length - 1);
  document.querySelectorAll('#frames .frame').forEach((el, n) => {
    el.classList.toggle('active', n === state.frame);
  });
  refreshLayerThumbs(); // layer panel thumbnails track the edited frame
  updateStatus();
  render();
}

/** Insert a frame after the current one and switch to it. */
function insertFrame(f) {
  state.frames.splice(state.frame + 1, 0, f);
  renderFrames();
  selectFrame(state.frame + 1);
}

const addFrame = () => insertFrame(makeFrame());

/** Duplicate = the real animation workflow: copy the pose, then nudge it.
 *  (Freeform planes copy canvas-to-canvas via makePlane's drawImage path.) */
function dupFrame() {
  commitFloat(); // so the duplicate includes what's being moved
  insertFrame(makeFrame(cur().layers.map(
    (l) => (state.mode === 'free' ? l.canvas : l.pixels.slice()))));
}

function deleteFrame() {
  commitFloat();
  const hasArt = cur().layers.some(planeHasArt);
  if (hasArt && !confirm(`Delete frame ${state.frame + 1}? This can't be undone.`)) return;
  state.frames.splice(state.frame, 1);
  if (!state.frames.length) state.frames.push(makeFrame()); // never zero frames
  renderFrames();
  selectFrame(Math.min(state.frame, state.frames.length - 1));
  updateUI(); // history entries for the deleted frame are skipped by applyHistory
}

/** Swap the current frame with a neighbor (dir: -1 = left, +1 = right). */
function moveFrame(dir) {
  commitFloat();
  const i = state.frame;
  const j = i + dir;
  if (j < 0 || j >= state.frames.length) return;
  [state.frames[i], state.frames[j]] = [state.frames[j], state.frames[i]];
  renderFrames();
  selectFrame(j);
}

/** Redraw one frame's strip thumbnail (call after any edit to that frame). */
function updateThumb(f) {
  if (!f.thumb) return;
  const g = f.thumb.getContext('2d');
  g.imageSmoothingEnabled = state.mode === 'free'; // crisp pixels vs smooth art
  g.clearRect(0, 0, f.thumb.width, f.thumb.height);
  g.drawImage(f.canvas, 0, 0, f.thumb.width, f.thumb.height);
}

/** Rebuild the whole frame strip (after add/delete/reorder/new project). */
function renderFrames() {
  const box = $('frames');
  box.innerHTML = '';
  const scale = Math.min(THUMB / state.width, THUMB / state.height);
  state.frames.forEach((f, i) => {
    const b = document.createElement('button');
    b.className = 'frame' + (i === state.frame ? ' active' : '');
    b.title = `Frame ${i + 1}`;
    const t = document.createElement('canvas');
    t.width = Math.max(1, Math.round(state.width * scale));
    t.height = Math.max(1, Math.round(state.height * scale));
    f.thumb = t;
    updateThumb(f);
    const n = document.createElement('span');
    n.textContent = i + 1;
    b.append(t, n);
    b.addEventListener('click', () => selectFrame(i));
    box.appendChild(b);
  });
}

$('btn-frame-add').addEventListener('click', addFrame);
$('btn-frame-dup').addEventListener('click', dupFrame);
$('btn-frame-del').addEventListener('click', deleteFrame);
$('btn-frame-left').addEventListener('click', () => moveFrame(-1));
$('btn-frame-right').addEventListener('click', () => moveFrame(1));

/** Wire a checkbox to a boolean state field; blur so shortcuts keep working. */
function bindToggle(id, key) {
  $(id).addEventListener('change', (e) => {
    state[key] = e.target.checked;
    e.target.blur();
    render();
  });
}
bindToggle('chk-onion-prev', 'onionPrev');
bindToggle('chk-onion-next', 'onionNext');
bindToggle('chk-origin', 'showOrigin');

/* --- Onion-skin settings popover (Procreate's Animation Assist knobs) ---
 * Reach, opacity, and the per-direction tints live behind the framebar's
 * Onion… button. The prev/next checkboxes above stay the master on/off
 * switches — this popover only shapes how the ghosts look. */

$('btn-onion-cfg').addEventListener('click', () => {
  $('onion-panel').hidden = !$('onion-panel').hidden;
});

/** Remember the popover's settings per browser (like brushes — view state
 *  lives in localStorage, never in project files). */
function persistOnion() {
  try {
    localStorage.setItem('ssm.onion', JSON.stringify({
      frames: state.onionFrames,
      opacity: state.onionOpacity,
      prevColor: state.onionPrevColor,
      nextColor: state.onionNextColor,
    }));
  } catch { /* storage full or blocked — settings just won't survive reload */ }
}

bindSliderPair('inp-onion-frames', 'onion-frames-num', (v) => {
  state.onionFrames = clamp(v || 1, 1, 8);
  persistOnion();
  render();
  return state.onionFrames;
});
bindSliderPair('inp-onion-opacity', 'onion-opacity-num', (v) => {
  state.onionOpacity = clamp(v || 45, 5, 100) / 100;
  persistOnion();
  render();
  return Math.round(state.onionOpacity * 100);
});
// Tint changes need no cache bookkeeping: drawGhost keys ghost caches by tint,
// so a new color simply misses the cache and rebuilds on the next render.
$('inp-onion-prev-color').addEventListener('input', (e) => {
  state.onionPrevColor = e.target.value;
  persistOnion();
  render();
});
$('inp-onion-next-color').addEventListener('input', (e) => {
  state.onionNextColor = e.target.value;
  persistOnion();
  render();
});

/** Bring back the onion-skin settings from localStorage and sync the popover.
 *  Fields are validated individually — a stale or hand-edited entry keeps the
 *  defaults for whatever doesn't parse instead of poisoning the whole set. */
function loadOnionSettings() {
  let s = null;
  try { s = JSON.parse(localStorage.getItem('ssm.onion') || 'null'); } catch { return; }
  if (!s || typeof s !== 'object') return;
  const isHex = (v) => typeof v === 'string' && /^#[0-9a-f]{6}$/i.test(v);
  if (Number.isInteger(s.frames)) state.onionFrames = clamp(s.frames, 1, 8);
  if (typeof s.opacity === 'number') state.onionOpacity = clamp(s.opacity, 0.05, 1);
  if (isHex(s.prevColor)) state.onionPrevColor = s.prevColor;
  if (isHex(s.nextColor)) state.onionNextColor = s.nextColor;
  $('inp-onion-frames').value = state.onionFrames;
  $('onion-frames-num').value = state.onionFrames;
  $('inp-onion-opacity').value = Math.round(state.onionOpacity * 100);
  $('onion-opacity-num').value = Math.round(state.onionOpacity * 100);
  $('inp-onion-prev-color').value = state.onionPrevColor;
  $('inp-onion-next-color').value = state.onionNextColor;
}

/* ======================================================================
 * Layers panel
 * ==================================================================== */
// Layers are project-wide (see state.layers): the panel edits the shared
// name/visibility/order, and structural ops splice every frame's plane list
// in lockstep. Layer ops are NOT undoable (same policy as frame ops); pixel
// history survives reorders and is skipped for deleted layers.

/** Switch which layer is being edited and re-highlight the panel. */
function selectLayer(i) {
  commitFloat(); // a floating selection belongs to the layer it was lifted from
  state.layer = clamp(i, 0, state.layers.length - 1);
  renderLayers();
  updateStatus();
}

const LAYER_THUMB = 34; // max thumbnail edge in the panel, px

/** Redraw one layer's panel thumbnail from the CURRENT frame's plane. */
function drawLayerThumb(li) {
  const t = state.layers[li].thumb;
  if (!t) return;
  const g = t.getContext('2d');
  g.imageSmoothingEnabled = state.mode === 'free'; // crisp pixels vs smooth art
  g.clearRect(0, 0, t.width, t.height);
  g.drawImage(cur().layers[li].canvas, 0, 0, t.width, t.height);
}

/** Refresh every layer thumbnail (after strokes, undo, or a frame switch —
 *  the thumbnails always show the frame being edited). */
function refreshLayerThumbs() {
  for (let li = 0; li < state.layers.length; li++) drawLayerThumb(li);
}

/** Rebuild the layer list, top layer first (art-app convention). */
function renderLayers() {
  const box = $('layers');
  box.innerHTML = '';
  const scale = Math.min(LAYER_THUMB / state.width, LAYER_THUMB / state.height);
  for (let i = state.layers.length - 1; i >= 0; i--) {
    const m = state.layers[i];
    const row = document.createElement('div');
    row.className = 'layer' + (i === state.layer ? ' active' : '');
    const thumb = document.createElement('canvas');
    thumb.className = 'layer-thumb';
    thumb.width = Math.max(1, Math.round(state.width * scale));
    thumb.height = Math.max(1, Math.round(state.height * scale));
    m.thumb = thumb; // meta object persists; saveProject picks its fields explicitly
    drawLayerThumb(i);
    const eye = document.createElement('input');
    eye.type = 'checkbox';
    eye.checked = m.visible;
    eye.title = 'Show / hide this layer (all frames)';
    eye.addEventListener('click', (ev) => ev.stopPropagation()); // don't also select
    eye.addEventListener('change', () => {
      m.visible = eye.checked;
      recompositeAll();
    });
    const name = document.createElement('span');
    name.textContent = m.name;
    name.title = 'Click to select · double-click to rename';
    // Non-default appearance at a glance: opacity %, blend initial, lock.
    // (The controls themselves live in the panel footer and edit whichever
    // layer is selected — rows just show that something is set.)
    const badges = document.createElement('span');
    badges.className = 'layer-badges';
    const parts = [];
    if (m.opacity !== 1) parts.push(`${Math.round(m.opacity * 100)}%`);
    if (m.blend !== 'normal') parts.push(m.blend[0].toUpperCase());
    if (m.alphaLock) parts.push('\u{1F512}');
    badges.textContent = parts.join(' ');
    row.addEventListener('click', () => selectLayer(i));
    row.addEventListener('dblclick', () => {
      const n = prompt('Layer name:', m.name);
      if (n && n.trim()) {
        m.name = n.trim();
        renderLayers();
        updateStatus();
      }
    });
    row.append(thumb, name, badges, eye);
    box.appendChild(row);
  }
  // The footer's appearance controls always show the SELECTED layer.
  const sel = state.layers[state.layer];
  $('inp-layer-opacity').value = Math.round(sel.opacity * 100);
  $('layer-opacity-num').value = Math.round(sel.opacity * 100);
  $('sel-layer-blend').value = sel.blend;
  $('btn-layer-lock').classList.toggle('active', sel.alphaLock === true);
}

/** Insert a (possibly duplicated) layer directly above the current one. */
function insertLayer(meta, planeFor) {
  commitFloat();
  if (state.layers.length >= MAX_LAYERS) {
    alert(`Projects support up to ${MAX_LAYERS} layers.`);
    return;
  }
  const at = state.layer + 1;
  state.layers.splice(at, 0, meta);
  for (const f of state.frames) {
    const p = makePlane(planeFor ? planeFor(f) : null);
    if (planeFor && state.mode === 'pixel') repaintLayer(p); // free: drawn by makePlane
    f.layers.splice(at, 0, p);
  }
  state.layer = at;
  recompositeAll();
  renderLayers();
  updateStatus();
}

const addLayer = () =>
  insertLayer({ name: `Layer ${state.layers.length + 1}`, visible: true,
                opacity: 1, blend: 'normal', alphaLock: false });

const dupLayer = () => {
  const m = state.layers[state.layer];
  const li = state.layer;
  insertLayer({ name: `${m.name} copy`, visible: m.visible,
                opacity: m.opacity, blend: m.blend, alphaLock: m.alphaLock },
              (f) => (state.mode === 'free' ? f.layers[li].canvas : f.layers[li].pixels.slice()));
};

function deleteLayer() {
  commitFloat();
  if (state.layers.length === 1) {
    alert('This is the only layer.');
    return;
  }
  const li = state.layer;
  const hasArt = state.frames.some((f) => planeHasArt(f.layers[li]));
  if (hasArt &&
      !confirm(`Delete layer "${state.layers[li].name}" from every frame? This can't be undone.`)) {
    return;
  }
  state.layers.splice(li, 1);
  for (const f of state.frames) f.layers.splice(li, 1);
  state.layer = Math.min(li, state.layers.length - 1);
  recompositeAll(); // history entries for the deleted planes are skipped by applyHistory
  renderLayers();
  updateStatus();
}

/** Swap the current layer with a neighbor (dir: +1 = up/toward viewer). */
function moveLayer(dir) {
  commitFloat();
  const i = state.layer;
  const j = i + dir;
  if (j < 0 || j >= state.layers.length) return;
  [state.layers[i], state.layers[j]] = [state.layers[j], state.layers[i]];
  for (const f of state.frames) {
    [f.layers[i], f.layers[j]] = [f.layers[j], f.layers[i]];
  }
  state.layer = j;
  recompositeAll();
  renderLayers();
}

$('btn-layer-add').addEventListener('click', addLayer);
$('btn-layer-dup').addEventListener('click', dupLayer);
$('btn-layer-del').addEventListener('click', deleteLayer);
$('btn-layer-up').addEventListener('click', () => moveLayer(1));
$('btn-layer-down').addEventListener('click', () => moveLayer(-1));

// Appearance controls (Phase 6d) — they edit the SELECTED layer's meta.
// Opacity previews live on just the edited frame while the slider drags
// ('input'); the full every-frame recomposite + thumbnail refresh waits for
// release ('change') so big multi-frame projects stay smooth under the drag.
// A typed value fires 'change' only, so it gets both steps at once.
bindSliderPair('inp-layer-opacity', 'layer-opacity-num', (v) => {
  const m = state.layers[state.layer];
  m.opacity = clamp(v || 0, 0, 100) / 100;
  recomposite(cur());
  render();
  return Math.round(m.opacity * 100);
});
for (const id of ['inp-layer-opacity', 'layer-opacity-num']) {
  $(id).addEventListener('change', () => {
    recompositeAll();
    renderLayers(); // row badges may have appeared/changed
  });
}
$('sel-layer-blend').addEventListener('change', (e) => {
  const m = state.layers[state.layer];
  m.blend = BLEND_MODES.includes(e.target.value) ? e.target.value : 'normal';
  recompositeAll();
  renderLayers();
});
$('btn-layer-lock').addEventListener('click', () => {
  const m = state.layers[state.layer];
  m.alphaLock = !m.alphaLock;
  renderLayers(); // no recomposite — the lock changes editing, not appearance
});
$('btn-layers-collapse').addEventListener('click', (e) => {
  const collapsed = $('layers-panel').classList.toggle('collapsed');
  e.currentTarget.innerHTML = collapsed ? '&#9656;' : '&#9662;';
});

// Floating panels (layers / brushes / preview) drag by their header — its
// buttons still just click. The first drag switches an edge-anchored panel
// to explicit left/top; it's clamped so the header always stays reachable
// inside the viewport.
function makePanelDraggable(panelId, headId) {
  $(headId).addEventListener('pointerdown', (e) => {
    if (e.target.closest('button')) return;
    const panel = $(panelId);
    const head = e.currentTarget;
    const start = panel.getBoundingClientRect();
    const bounds = wrap.getBoundingClientRect();
    const dx = e.clientX - start.left;
    const dy = e.clientY - start.top;
    const move = (ev) => {
      panel.style.left =
        clamp(ev.clientX - bounds.left - dx, 0, Math.max(0, bounds.width - start.width)) + 'px';
      panel.style.top =
        clamp(ev.clientY - bounds.top - dy, 0, Math.max(0, bounds.height - 36)) + 'px';
      panel.style.right = 'auto';
      panel.style.bottom = 'auto';
    };
    head.setPointerCapture(e.pointerId);
    head.addEventListener('pointermove', move);
    head.addEventListener('pointerup', () => head.removeEventListener('pointermove', move), { once: true });
    e.preventDefault();
  });
}
makePanelDraggable('layers-panel', 'layers-head');
makePanelDraggable('preview-panel', 'preview-head');

/* ======================================================================
 * Animation playback — plays IN the main canvas (plus an optional popup)
 * ==================================================================== */
// Playback swaps which composite render() blits: `playFrame` advances on a
// timer while `state.frame` — the frame being EDITED — never moves. That
// split is the whole pause story: the Pause button just stops the timer and
// you're back on your frame; clicking the canvas instead ADOPTS the frame
// that was showing (see it wrong, click it, fix it). Editing chrome hides
// during playback except onion ghosts, which follow their own toggles.
//
// The popup (#preview-panel, off by default, draggable like the layers
// panel) holds the old sidebar preview canvas: art-sized backing store (set
// in newProject), CSS-upscaled, checkerboard behind — one 1:1 drawImage.

const preview = $('preview');
const prevCtx = preview.getContext('2d');

let playing = false;
let playFrame = 0;    // playback position — independent of the edited frame
let playTimer = null;

/** Current FPS from the input, clamped to something sane. */
const fps = () => clamp(parseInt($('inp-fps').value, 10) || 8, 1, 60);

function drawPreview(f) {
  prevCtx.clearRect(0, 0, preview.width, preview.height);
  prevCtx.drawImage(f.canvas, 0, 0);
}

/** While stopped, the popup mirrors the frame being edited (live). */
function updatePreview() {
  if (!playing && cur() && !$('preview-panel').hidden) drawPreview(cur());
}

/** Outline the frame the player is showing (gold, distinct from the blue
 *  "being edited" outline). Passing -1 clears it. */
function markPlayFrame(i) {
  document.querySelectorAll('#frames .frame').forEach((el, n) => {
    el.classList.toggle('playing', n === i);
  });
}

function playTick() {
  playFrame = (playFrame + 1) % state.frames.length;
  markPlayFrame(playFrame);
  if (!$('preview-panel').hidden) drawPreview(state.frames[playFrame]);
  render(); // the main canvas is the player
}

function setPlaying(on) {
  if (on) commitFloat(); // a float belongs to the edited frame — land it first
  playing = on;
  $('btn-play').innerHTML = on ? '&#10074;&#10074; Pause' : '&#9654; Play';
  clearInterval(playTimer);
  playTimer = null;
  if (on) {
    playFrame = state.frame; // start the loop from where the user is working
    markPlayFrame(playFrame);
    playTimer = setInterval(playTick, 1000 / fps());
  } else {
    markPlayFrame(-1);
    updatePreview();
  }
  // newProject pauses before it has built any frames — nothing to draw yet.
  if (state.frames.length) render();
}

$('btn-play').addEventListener('click', () => setPlaying(!playing));

// 'change' fires on Enter/blur; restarting the interval applies the new speed
// mid-playback. Blur so keyboard shortcuts work again immediately.
$('inp-fps').addEventListener('change', (e) => {
  e.target.value = fps();
  if (playing) setPlaying(true);
  e.target.blur();
});

// --- The floating preview popup: toggled from the framebar, off by default.
$('chk-preview').addEventListener('change', (e) => {
  $('preview-panel').hidden = !e.target.checked;
  e.target.blur();
  if (e.target.checked) drawPreview(playing ? state.frames[playFrame] : cur());
});
$('btn-preview-close').addEventListener('click', () => {
  $('preview-panel').hidden = true;
  $('chk-preview').checked = false;
});

/* ======================================================================
 * Export (PNG sprite sheet) & project save/load (JSON)
 * ==================================================================== */

// Bump when the save format changes; loaders can then migrate old files.
// v1: frames = [pixelArray]. v2: layers metadata + frames = [[layerPixels]].
// v3: + mode field; freeform planes are PNG data-URL strings, not arrays.
const PROJECT_VERSION = 3;

/** Trigger a browser download of a Blob. */
function download(filename, blob) {
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = filename;
  a.click();
  // Delay revoking: some browsers cancel the download if revoked immediately.
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
}

/**
 * Compose all frames onto one canvas at native resolution and download it.
 * Layout comes from the "Cols" input: 0/blank = every frame in one horizontal
 * strip (the default game-engine-friendly layout), N = grid N frames wide.
 */
function exportSheet() {
  commitFloat();
  const n = state.frames.length;
  let cols = parseInt($('inp-cols').value, 10) || 0;
  if (cols <= 0 || cols > n) cols = n;
  const rows = Math.ceil(n / cols);
  // Browsers hard-cap canvas dimensions (~32,767px per side, ~268M px area);
  // past that toBlob silently yields nothing. Large frames hit this fast.
  const sw = cols * state.width;
  const sh = rows * state.height;
  if (sw > 32767 || sh > 32767 || sw * sh > 268435456) {
    alert(`This sheet would be ${sw}×${sh}px — too large for the browser to compose.\n` +
          `Try a different Cols value to make the sheet squarer, or fewer/smaller frames.`);
    return;
  }
  const sheet = document.createElement('canvas');
  sheet.width = sw;
  sheet.height = sh;
  const g = sheet.getContext('2d');
  state.frames.forEach((f, i) => {
    g.drawImage(f.canvas, (i % cols) * state.width, Math.floor(i / cols) * state.height);
  });
  sheet.toBlob(
    (blob) => download(`spritesheet-${state.width}x${state.height}-${n}f.png`, blob),
    'image/png'
  );
}

/* ---- Animation exports (encoders live in export.js) ---- */

const exportBase = () => `${state.width}x${state.height}-${state.frames.length}f`;

/** Every frame PNG-encoded by the browser, as Uint8Arrays (for APNG/ZIP). */
function framePNGs() {
  return Promise.all(state.frames.map((f) => new Promise((resolve, reject) => {
    f.canvas.toBlob(async (b) => {
      if (!b) return reject(new Error('PNG encoding failed.'));
      resolve(new Uint8Array(await b.arrayBuffer()));
    }, 'image/png');
  })));
}

/** Shared wrapper: disable the button while an export runs, surface errors. */
async function runExport(btn, fn) {
  commitFloat(); // exports read the layers; land any floating selection first
  btn.disabled = true;
  try {
    await fn();
  } catch (err) {
    alert('Export failed: ' + err.message);
  } finally {
    btn.disabled = false;
  }
}

$('btn-export-gif').addEventListener('click', (e) => runExport(e.currentTarget, () => {
  // GIF is palette-based (≤256 colors) with 1-bit transparency. Freeform art
  // — and pixel art once layers blend or go translucent — routinely exceeds
  // both: colors snap to the kept palette (visible banding on gradients) and
  // soft edges flatten at alpha 128. Warn before that quietly mangles art;
  // plain pixel projects skip the prompt, GIF is lossless for them.
  if ((state.mode === 'free' || !layersDefault()) &&
      !confirm('GIF only supports 256 colors and hard transparency — smooth gradients will band and soft edges will flatten.\nFor a lossless animation with full alpha, use Export APNG.\n\nExport GIF anyway?')) {
    return;
  }
  const bytes = Exporters.encodeGIF(
    state.frames.map(compositePixels), state.width, state.height, fps());
  download(`animation-${exportBase()}.gif`, new Blob([bytes], { type: 'image/gif' }));
}));

$('btn-export-apng').addEventListener('click', (e) => runExport(e.currentTarget, async () => {
  const bytes = Exporters.encodeAPNG(await framePNGs(), fps());
  // .png, not .apng: an APNG is a valid PNG, and .png uploads anywhere.
  download(`animation-${exportBase()}.png`, new Blob([bytes], { type: 'image/png' }));
}));

$('btn-export-video').addEventListener('click', (e) => runExport(e.currentTarget, async () => {
  const { blob, ext } = await Exporters.recordVideo(
    state.frames.map((f) => f.canvas), state.width, state.height, fps(),
    state.mode === 'free'); // smooth upscaling for painted art, crisp for pixels
  download(`animation-${exportBase()}.${ext}`, blob);
}));

$('btn-export-zip').addEventListener('click', (e) => runExport(e.currentTarget, async () => {
  const pngs = await framePNGs();
  const pad = String(pngs.length).length;
  const files = pngs.map((data, i) => ({
    name: `frame-${String(i + 1).padStart(pad, '0')}.png`,
    data,
  }));
  download(`frames-${exportBase()}.zip`,
    new Blob([Exporters.encodeZIP(files)], { type: 'application/zip' }));
}));

/** Serialize the whole project (frames, layers, palette, size, fps) and download it. */
function saveProject() {
  commitFloat(); // a floating selection should be in the saved pixels
  const data = {
    app: 'sprite-sheet-maker', // marker so we can recognize our own files
    version: PROJECT_VERSION,
    mode: state.mode,
    width: state.width,
    height: state.height,
    fps: fps(),
    palette: state.palette,
    // Appearance fields (6d) ride along in v3: parseProject treats them as
    // optional-with-defaults, so files from before 6d still load unchanged.
    layers: state.layers.map((m) => ({
      name: m.name, visible: m.visible,
      opacity: m.opacity, blend: m.blend, alphaLock: m.alphaLock,
    })),
    // Pixel planes save as hex arrays (diff-able, hand-fixable). Freeform
    // planes save as PNG data-URLs — the plane's canvas is the truth there,
    // and lossless PNG is hugely smaller than a per-pixel string array.
    frames: state.frames.map((f) => f.layers.map((l) =>
      state.mode === 'free' ? l.canvas.toDataURL('image/png') : l.pixels)),
  };
  const blob = new Blob([JSON.stringify(data)], { type: 'application/json' });
  download(`sprite-project-${state.width}x${state.height}-${state.frames.length}f.json`, blob);
}

/**
 * Decode one saved freeform plane (a PNG data-URL) into an Image, which
 * makePlane() stamps straight onto the plane's canvas — lossless, full
 * alpha. Null = not a valid plane for this project's dimensions.
 */
async function decodePlane(url, w, h) {
  if (typeof url !== 'string' || !url.startsWith('data:image/')) return null;
  const img = new Image();
  try {
    img.src = url;
    await img.decode();
  } catch { return null; }
  return img.naturalWidth === w && img.naturalHeight === h ? img : null;
}

/**
 * Parse and validate saved-project JSON. Returns {w, h, frames, layers,
 * palette, fps, mode} — frames nested [frame][layer] — or null if the file
 * isn't a (sane) project. v1 files (flat pixel array per frame) are migrated
 * to a single layer; v1/v2 predate modes and load as pixel projects. Every
 * pixel is checked against #rrggbb — anything unexpected becomes transparent
 * rather than crashing. Async because freeform planes are PNGs to decode.
 */
async function parseProject(text) {
  let d;
  try { d = JSON.parse(text); } catch { return null; }
  if (!d || d.app !== 'sprite-sheet-maker' || !Array.isArray(d.frames) || !d.frames.length) return null;
  const w = parseInt(d.width, 10);
  const h = parseInt(d.height, 10);
  if (!(w >= 1 && w <= MAX_W && h >= 1 && h <= MAX_H)) return null;
  const mode = d.version >= 3 && d.mode === 'free' ? 'free' : 'pixel';
  const isColor = (c) => typeof c === 'string' && /^#[0-9a-f]{6}$/i.test(c);
  const cleanPlane = (px) =>
    Array.isArray(px) && px.length === w * h
      ? px.map((c) => (isColor(c) ? c.toLowerCase() : null))
      : null;

  let layers;
  const frames = [];
  if (!d.version || d.version < 2) {
    // v1: one flat pixel array per frame — becomes a single-layer project.
    layers = [{ name: 'Layer 1', visible: true }];
    for (const px of d.frames) {
      const p = cleanPlane(px);
      if (!p) return null;
      frames.push([p]);
    }
  } else {
    if (!Array.isArray(d.layers) || !d.layers.length || d.layers.length > MAX_LAYERS) return null;
    layers = d.layers.map((m, i) => ({
      name: m && typeof m.name === 'string' && m.name.trim() ? m.name.trim() : `Layer ${i + 1}`,
      visible: !m || m.visible !== false,
      // 6d appearance fields — absent in pre-6d files, so default rather
      // than reject (this is why the format stayed at version 3).
      opacity: m && typeof m.opacity === 'number' && m.opacity >= 0 && m.opacity <= 1
        ? m.opacity : 1,
      blend: m && BLEND_MODES.includes(m.blend) ? m.blend : 'normal',
      alphaLock: !!m && m.alphaLock === true,
    }));
    for (const fl of d.frames) {
      if (!Array.isArray(fl) || fl.length !== layers.length) return null;
      const planes = [];
      for (const px of fl) {
        const p = mode === 'free' ? await decodePlane(px, w, h) : cleanPlane(px);
        if (!p) return null;
        planes.push(p);
      }
      frames.push(planes);
    }
  }
  const palette = Array.isArray(d.palette) ? d.palette.filter(isColor).slice(0, MAX_PALETTE) : [];
  return {
    w, h, frames, layers, mode,
    palette: palette.length ? palette : null,
    fps: parseInt(d.fps, 10) || null,
  };
}

/**
 * Import a PNG or JPEG as the base to work from (import only — we never
 * export JPEG; lossy compression would smear pixel art). The image becomes
 * a new project in whichever MODE the File-menu picker shows: mode is
 * locked at creation, so the picker is the only way to say "import this as
 * freeform". One frame, canvas sized to the image — unless it looks like a
 * horizontal sprite strip (width an exact multiple of height, i.e. what
 * exportSheet() produces for square frames), in which case we offer to
 * slice it back into frames. A strip too wide to import whole (over MAX_W)
 * skips that choice: the user is told it has to load as separate frames,
 * and it does — only images whose FRAMES don't fit are rejected outright.
 *
 * Pixel mode: alpha < 128 becomes transparent, partial alpha flattens to
 * opaque — the pixel format is #rrggbb-or-null and can't hold more.
 * Freeform: the image is drawn straight into each plane's canvas, so
 * partial alpha survives exactly (JPEGs simply have none to preserve).
 */
async function importImage(file) {
  const img = new Image();
  const url = URL.createObjectURL(file);
  try {
    img.src = url;
    await img.decode();
  } catch {
    alert('Could not read that image file.');
    return;
  } finally {
    URL.revokeObjectURL(url);
  }
  const iw = img.naturalWidth;
  const ih = img.naturalHeight;

  // Sprite-strip heuristic: N square frames side by side.
  let frameW = iw;
  let count = 1;
  const sliceable = ih <= MAX_H && iw % ih === 0 && iw / ih > 1;
  if (sliceable && iw > MAX_W) {
    // Too wide to be one canvas, but its frames fit — offering the usual
    // slice-or-whole choice would make "whole" a dead end, so just say
    // what has to happen and slice. (ih ≤ MAX_H ≤ MAX_W, so frames fit.)
    alert(`This image is ${iw}px wide — over the ${MAX_W}px canvas limit — but it slices cleanly into ${iw / ih} frames of ${ih}×${ih}.\nIt will be imported as separate frames.`);
    frameW = ih;
    count = iw / ih;
  } else if (sliceable &&
      confirm(`This image looks like a sprite strip of ${iw / ih} frames (${ih}×${ih} each).\nOK = slice into frames, Cancel = import as one image.`)) {
    frameW = ih;
    count = iw / ih;
  }
  if (frameW > MAX_W || ih > MAX_H) {
    alert(`Image is too large: max canvas size is ${MAX_W}×${MAX_H} pixels.`);
    return;
  }
  if (anyArt() && !confirm('Import image? Current frames will be replaced.')) return;

  if ($('mode-free').checked) {
    // Freeform planes take anything drawImage accepts — hand each frame a
    // canvas holding its slice of the image (the whole image when count=1).
    // No ImageData round-trip, so every alpha value carries over untouched.
    const frames = [];
    for (let f = 0; f < count; f++) {
      const c = document.createElement('canvas');
      c.width = frameW;
      c.height = ih;
      c.getContext('2d').drawImage(img, -f * frameW, 0);
      frames.push([c]); // one layer per frame
    }
    newProject(frameW, ih, frames, null, null, null, 'free');
    return;
  }

  // Pixel mode: rasterize one frame at a time through a frame-sized canvas.
  // A strip can be wider than the browser's canvas cap (~32,767px) even when
  // its individual frames fit, so never stage the whole image on one canvas
  // — decoded images aren't bound by that cap, drawImage from them is fine.
  const c = document.createElement('canvas');
  c.width = frameW;
  c.height = ih;
  const g = c.getContext('2d');
  const toHex = (v) => v.toString(16).padStart(2, '0');
  const frames = [];
  for (let f = 0; f < count; f++) {
    g.clearRect(0, 0, frameW, ih);
    g.drawImage(img, -f * frameW, 0);
    const data = g.getImageData(0, 0, frameW, ih).data; // RGBA quads, row-major
    const px = new Array(frameW * ih);
    for (let i = 0; i < px.length; i++) {
      const o = i * 4;
      px[i] = data[o + 3] < 128
        ? null
        : `#${toHex(data[o])}${toHex(data[o + 1])}${toHex(data[o + 2])}`;
    }
    frames.push(px);
  }
  newProject(frameW, ih, frames.map((px) => [px])); // one layer per frame
}

$('btn-export').addEventListener('click', exportSheet);
$('btn-save').addEventListener('click', saveProject);
$('btn-load').addEventListener('click', () => $('inp-file').click());

// One Load button for both file kinds: images (PNG/JPEG) import as artwork,
// anything else is treated as a saved project.
$('inp-file').addEventListener('change', async (e) => {
  const file = e.target.files[0];
  e.target.value = ''; // so choosing the same file again still fires 'change'
  if (!file) return;
  if (/^image\/(png|jpeg)$/.test(file.type) || /\.(png|jpe?g)$/i.test(file.name)) {
    importImage(file);
    return;
  }
  const proj = await parseProject(await file.text());
  if (!proj) {
    alert('That file is not a Sprite Sheet Maker project.');
    return;
  }
  if (anyArt() && !confirm('Load project? Current frames will be replaced.')) return;
  newProject(proj.w, proj.h, proj.frames, proj.layers, proj.palette, proj.fps, proj.mode);
});

/* ======================================================================
 * Color & palette UI
 * ==================================================================== */

/** Make `c` the active color and sync the picker + swatch highlight. */
function selectColor(c) {
  state.color = c;
  $('inp-color').value = c;
  renderPalette();
}

/** Auto-add a color to the palette the first time it's actually painted with. */
function addUsedColor(c) {
  if (state.palette.includes(c)) return;
  state.palette.push(c);
  if (state.palette.length > MAX_PALETTE) state.palette.shift();
  renderPalette();
}

/** Rebuild the swatch grid. Small enough that full rebuilds are simplest. */
function renderPalette() {
  const pal = $('palette');
  pal.innerHTML = '';
  for (const c of state.palette) {
    const b = document.createElement('button');
    b.className = 'swatch' + (c === state.color ? ' active' : '');
    b.style.background = c;
    b.title = c;
    b.addEventListener('click', () => selectColor(c));
    b.addEventListener('contextmenu', (ev) => {
      ev.preventDefault();
      state.palette = state.palette.filter((x) => x !== c);
      renderPalette();
    });
    pal.appendChild(b);
  }
}

// 'input' fires continuously while dragging inside the picker — live preview.
$('inp-color').addEventListener('input', (e) => selectColor(e.target.value));

/* ======================================================================
 * Brush library panel (Phase 7) — freeform brush picker & PNG imports
 * ==================================================================== */
// Procreate-style floating panel: one row per brush (name over a white
// stroke swatch drawn with the real tip + dynamics), the selected row
// highlighted, [+] imports an image as a new tip, imported rows carry a ✕.
// Imported brushes persist in localStorage as normalized TIP_SIZE mask
// PNGs; the selected brush id persists there too. Neither ever lands in
// project files — brushes are tool state, like tip size.

const BRUSH_STORE = 'ssm.brushes';

function persistBrushes() {
  try {
    localStorage.setItem(BRUSH_STORE, JSON.stringify(
      brushes.filter((b) => b.imported).map((b) => ({
        id: b.id,
        name: b.name,
        url: b.mask.toDataURL('image/png'),
      }))));
    localStorage.setItem('ssm.brush', state.brush);
  } catch { /* storage full or blocked — imports just won't survive reload */ }
}

/** Bring back imported brushes (and the selection) from localStorage. */
async function loadStoredBrushes() {
  let saved = null;
  let sel = null;
  try {
    saved = JSON.parse(localStorage.getItem(BRUSH_STORE) || 'null');
    sel = localStorage.getItem('ssm.brush');
  } catch { return; }
  if (Array.isArray(saved)) {
    for (const s of saved) {
      if (!s || typeof s.url !== 'string' || !s.url.startsWith('data:image/')) continue;
      const img = new Image();
      try {
        img.src = s.url;
        await img.decode();
      } catch { continue; } // a corrupt entry shouldn't take the rest down
      const mask = document.createElement('canvas');
      mask.width = mask.height = TIP_SIZE;
      mask.getContext('2d').drawImage(img, 0, 0, TIP_SIZE, TIP_SIZE);
      brushes.push({
        id: typeof s.id === 'string' ? s.id : `imp-${Math.random()}`,
        name: typeof s.name === 'string' && s.name ? s.name : 'Imported',
        kind: 'texture', imported: true,
        rotJitter: 0, sizeJitter: 0, follow: false,
        mask,
      });
    }
  }
  if (sel && brushes.some((b) => b.id === sel)) state.brush = sel;
  renderBrushList();
  syncBrushUI();
}

/**
 * Paint one library row's swatch: the brush's own tip stamped in white
 * along a gentle S-curve with pressure tapering in and out — the same
 * dynamics real strokes use, so what the row shows is what paint does.
 */
function drawBrushPreview(cv, b) {
  const g = cv.getContext('2d');
  const w = cv.width;
  const h = cv.height;
  g.clearRect(0, 0, w, h);
  const size = h * 0.62;
  const tip = buildTip(b, '#f4f4f4', Math.max(2, Math.round(size)), 0.8);
  const pad = size / 2 + 2;
  const spacing = Math.max(1, size * STAMP_SPACING);
  for (let x = pad; x <= w - pad; x += spacing) {
    const t = (x - pad) / (w - 2 * pad);                    // 0..1 along the swatch
    const y = h / 2 + Math.sin(t * Math.PI * 2) * h * 0.16; // the S
    const d = size * (0.25 + 0.75 * Math.sin(t * Math.PI)); // pressure taper
    if (b.kind === 'texture') {
      const s = d * (1 + (Math.random() * 2 - 1) * b.sizeJitter);
      const ang = (Math.random() * 2 - 1) * Math.PI * b.rotJitter; // travel is ~horizontal, so follow adds 0
      g.save();
      g.translate(x, y);
      g.rotate(ang);
      g.drawImage(tip, -s / 2, -s / 2, s, s);
      g.restore();
    } else {
      g.drawImage(tip, x - d / 2, y - d / 2, d, d);
    }
  }
}

/** Rebuild the library list (small enough that full rebuilds are simplest). */
function renderBrushList() {
  const box = $('brush-list');
  box.innerHTML = '';
  for (const b of brushes) {
    const row = document.createElement('div');
    row.className = 'brush' + (b.id === state.brush ? ' active' : '');
    const name = document.createElement('span');
    name.textContent = b.name;
    row.appendChild(name);
    if (b.imported) {
      const del = document.createElement('button');
      del.className = 'brush-del';
      del.textContent = '✕';
      del.title = 'Delete this imported brush';
      del.addEventListener('click', (ev) => {
        ev.stopPropagation(); // don't also select the row
        if (!confirm(`Delete brush "${b.name}"?`)) return;
        brushes = brushes.filter((x) => x !== b);
        if (state.brush === b.id) state.brush = 'round';
        persistBrushes();
        renderBrushList();
        syncBrushUI();
      });
      row.appendChild(del);
    }
    const swatch = document.createElement('canvas');
    swatch.className = 'brush-swatch';
    swatch.width = 168;
    swatch.height = 34;
    drawBrushPreview(swatch, b);
    row.appendChild(swatch);
    row.addEventListener('click', () => selectBrush(b.id));
    box.appendChild(row);
  }
}

function selectBrush(id) {
  state.brush = id;
  persistBrushes(); // remembers the selection across sessions
  renderBrushList();
  syncBrushUI();
}

/** Keep the brush-box chrome honest: the library button names the current
 *  brush, and the hardness slider only exists for the round tip. */
function syncBrushUI() {
  $('btn-brush-lib').textContent = `Brush: ${curBrush().name} ▾`;
  $('hardness-box').hidden = curBrush().kind !== 'round';
}

/**
 * Import an image as a brush tip. Normalized to a TIP_SIZE mask, fit
 * centered; paint coverage = alpha × luminance (white/opaque paints,
 * black/transparent doesn't — Procreate's tip convention, and it makes
 * both transparent-PNG tips and black-on-white scans behave). Imports
 * stamp as authored — no jitter; the presets carry the organic dynamics.
 */
async function importBrushFile(file) {
  const img = new Image();
  const url = URL.createObjectURL(file);
  try {
    img.src = url;
    await img.decode();
  } catch {
    alert('Could not read that image file.');
    return;
  } finally {
    URL.revokeObjectURL(url);
  }
  const c = document.createElement('canvas');
  c.width = c.height = TIP_SIZE;
  const g = c.getContext('2d');
  const sc = Math.min(TIP_SIZE / img.naturalWidth, TIP_SIZE / img.naturalHeight);
  const w = img.naturalWidth * sc;
  const h = img.naturalHeight * sc;
  g.drawImage(img, (TIP_SIZE - w) / 2, (TIP_SIZE - h) / 2, w, h);
  const d = g.getImageData(0, 0, TIP_SIZE, TIP_SIZE);
  for (let i = 0; i < d.data.length; i += 4) {
    const luma = 0.2126 * d.data[i] + 0.7152 * d.data[i + 1] + 0.0722 * d.data[i + 2];
    d.data[i + 3] = (d.data[i + 3] / 255) * luma;
    d.data[i] = d.data[i + 1] = d.data[i + 2] = 255;
  }
  g.putImageData(d, 0, 0);
  const brush = {
    id: `imp-${Date.now()}`,
    name: (file.name || 'Imported').replace(/\.[^.]+$/, '') || 'Imported',
    kind: 'texture', imported: true,
    rotJitter: 0, sizeJitter: 0, follow: false,
    mask: c,
  };
  brushes.push(brush);
  selectBrush(brush.id); // also persists
}

$('btn-brush-lib').addEventListener('click', () => {
  $('brush-panel').hidden = !$('brush-panel').hidden;
});
$('btn-brush-close').addEventListener('click', () => {
  $('brush-panel').hidden = true;
});
$('btn-brush-import').addEventListener('click', () => $('inp-brush-file').click());
$('inp-brush-file').addEventListener('change', async (e) => {
  const file = e.target.files[0];
  e.target.value = ''; // so re-importing the same file still fires 'change'
  if (file) await importBrushFile(file);
});

// The panel drags by its header, same deal as the layers panel.
makePanelDraggable('brush-panel', 'brush-head');

/* ======================================================================
 * Toolbar / status bar / top bar wiring
 * ==================================================================== */

function selectTool(t) {
  // Smudge drags RGBA around — meaningless on hex-or-null pixel planes.
  if (t === 'smudge' && state.mode !== 'free') {
    flashHint('Smudge is a freeform-mode tool.');
    return;
  }
  if (t !== 'select' && (selection || floating)) {
    commitFloat(); // leaving the Select tool lands and drops the selection
    selection = null;
    syncSelectBar();
    render();
  }
  state.tool = t;
  document.querySelectorAll('#toolbar .tool').forEach((b) => {
    b.classList.toggle('active', b.dataset.tool === t);
  });
  wrap.classList.toggle('pan-tool', t === 'pan'); // grab cursor over the canvas
  // The smudge tool swaps the Opacity slider for its Strength slider — a tool
  // that deposits no color has no opacity. (Both rows are freeform-only; in
  // pixel mode the mode-free CSS hides them regardless of these flags.)
  $('opacity-box').hidden = t === 'smudge';
  $('strength-box').hidden = t !== 'smudge';
  $('st-tool').textContent = toolLabel();
}

document.querySelectorAll('#toolbar .tool').forEach((b) => {
  b.addEventListener('click', () => {
    // Procreate muscle memory: tapping the already-active Brush again opens
    // the library — and likewise Smudge, which smears through the same tips
    // (freeform only — pixel mode has no brush library).
    if (['brush', 'smudge'].includes(b.dataset.tool) &&
        state.tool === b.dataset.tool && state.mode === 'free') {
      $('brush-panel').hidden = !$('brush-panel').hidden;
    }
    selectTool(b.dataset.tool);
  });
});

// The status bar shows the tip size when it matters (tip tools, > 1px).
const toolLabel = () =>
  ['brush', 'eraser', 'smudge'].includes(state.tool) && state.brushSize > 1
    ? `${state.tool} ${state.brushSize}px`
    : state.tool;

/** The mode's tip-size ceiling (freeform canvases warrant fatter brushes). */
const maxBrush = () => (state.mode === 'free' ? MAX_BRUSH_FREE : MAX_BRUSH);

/** Set the brush/eraser tip size, keeping slider, number box & status in sync. */
function setBrushSize(n) {
  state.brushSize = clamp(n, 1, maxBrush());
  $('inp-brush-size').value = state.brushSize;
  $('size-num').value = state.brushSize;
  $('st-tool').textContent = toolLabel();
  render(); // the hover footprint changed size
}

function setBrushShape(s) {
  state.brushShape = s;
  $('shape-square').classList.toggle('active', s === 'square');
  $('shape-circle').classList.toggle('active', s === 'circle');
  render();
}

/**
 * Every slider is paired with a number box for exact-value entry ("brush
 * size 100", not "wiggle until close"). Both drive ONE apply function that
 * clamps and returns the value actually used, which is then echoed into
 * both controls — so typing 9999 lands on the real ceiling, visibly.
 * Sliders fire live ('input'); the box applies on Enter/blur ('change'),
 * then blurs so keyboard shortcuts come back.
 */
function bindSliderPair(sliderId, numId, apply) {
  const echo = (v) => {
    $(sliderId).value = v;
    $(numId).value = v;
  };
  $(sliderId).addEventListener('input',
    (e) => echo(apply(parseInt(e.target.value, 10))));
  $(numId).addEventListener('change', (e) => {
    echo(apply(parseInt(e.target.value, 10)));
    e.target.blur();
  });
}

bindSliderPair('inp-brush-size', 'size-num', (v) => {
  setBrushSize(v || 1); // does its own clamp + slider/box echo
  return state.brushSize;
});
$('shape-square').addEventListener('click', () => setBrushShape('square'));
$('shape-circle').addEventListener('click', () => setBrushShape('circle'));

// Freeform-only stroke settings (hidden in pixel mode via body.mode-free).
bindSliderPair('inp-brush-opacity', 'opacity-num', (v) => {
  state.brushOpacity = clamp(v || 100, 1, 100) / 100;
  return Math.round(state.brushOpacity * 100);
});
bindSliderPair('inp-smudge-strength', 'strength-num', (v) => {
  state.smudgeStrength = clamp(v || 50, 1, 100) / 100;
  return Math.round(state.smudgeStrength * 100);
});
bindSliderPair('inp-brush-hardness', 'hardness-num', (v) => {
  state.brushHardness = clamp(v || 0, 0, 100) / 100;
  return Math.round(state.brushHardness * 100);
});
bindSliderPair('inp-fill-tol', 'tolerance-num', (v) => {
  state.fillTolerance = clamp(v || 0, 0, 100) / 100;
  return Math.round(state.fillTolerance * 100);
});

function updateStatus() {
  $('st-coords').textContent = hover ? `${hover.x}, ${hover.y}` : '—';
  $('st-frame').textContent =
    `frame ${state.frame + 1}/${state.frames.length} · ${state.layers[state.layer].name}`;
}

// Briefly replace the status-bar hint with a message, then restore it.
const defaultHint = $('st-hint').textContent;
let hintTimer = null;
function flashHint(msg) {
  $('st-hint').textContent = msg;
  clearTimeout(hintTimer);
  hintTimer = setTimeout(() => { $('st-hint').textContent = defaultHint; }, 2500);
}

/** Refresh everything cheap outside the canvas: buttons, zoom label, status. */
function updateUI() {
  $('btn-undo').disabled = !state.undo.length;
  $('btn-redo').disabled = !state.redo.length;
  // Below 1× a tenth isn't enough precision (0.03× would read as "0×").
  $('zoom-label').textContent = state.zoom < 1
    ? `${state.zoom.toFixed(2)}×`
    : `${Math.round(state.zoom * 10) / 10}×`;
  updateStatus();
}

// File menu: a small dropdown holding New / Save / Load.
const fileMenu = $('file-menu');
$('btn-file').addEventListener('click', (e) => {
  e.stopPropagation(); // or the document click handler below would re-close it
  e.currentTarget.blur(); // stopPropagation also skips the global blur handler
  fileMenu.hidden = !fileMenu.hidden;
});
// Clicking anywhere outside the menu closes it; clicking inside keeps it open
// (so the W/H inputs are usable) — except the action buttons, which close it
// themselves below.
document.addEventListener('click', (e) => {
  if (!fileMenu.hidden && !fileMenu.contains(e.target)) fileMenu.hidden = true;
});
for (const id of ['btn-new', 'btn-save', 'btn-load', 'btn-export',
                  'btn-export-gif', 'btn-export-apng', 'btn-export-video', 'btn-export-zip']) {
  $(id).addEventListener('click', () => { fileMenu.hidden = true; });
}

$('btn-undo').addEventListener('click', undo);
$('btn-redo').addEventListener('click', redo);
$('btn-zoom-in').addEventListener('click', () => setZoom(state.zoom * 1.2, viewW / 2, viewH / 2));
$('btn-zoom-out').addEventListener('click', () => setZoom(state.zoom / 1.2, viewW / 2, viewH / 2));
$('btn-fit').addEventListener('click', fitView);

// Size presets: picking one just fills in W/H — New still creates the
// project. Hand-editing W/H flips the select back to its placeholder so it
// never claims a size it doesn't match.
$('sel-preset').addEventListener('change', (e) => {
  if (!e.target.value) return;
  const [w, h] = e.target.value.split('x');
  $('inp-w').value = w;
  $('inp-h').value = h;
});
for (const id of ['inp-w', 'inp-h']) {
  $(id).addEventListener('input', () => { $('sel-preset').value = ''; });
}

$('btn-new').addEventListener('click', () => {
  const w = clamp(parseInt($('inp-w').value, 10) || 32, 1, MAX_W);
  const h = clamp(parseInt($('inp-h').value, 10) || 32, 1, MAX_H);
  $('inp-w').value = w;
  $('inp-h').value = h;
  if (anyArt() && !confirm('Start a new canvas? All current frames will be lost.')) return;
  newProject(w, h, null, null, null, null, $('mode-free').checked ? 'free' : 'pixel');
});

/* ======================================================================
 * Viewport sizing & startup
 * ==================================================================== */

/** Match the canvas backing store to the container size and pixel density. */
function resize() {
  dpr = window.devicePixelRatio || 1;
  viewW = wrap.clientWidth;
  viewH = wrap.clientHeight;
  view.width = Math.round(viewW * dpr);
  view.height = Math.round(viewH * dpr);
  view.style.width = viewW + 'px';
  view.style.height = viewH + 'px';
  // First time we know the real viewport size, center the artwork in it.
  if (!fitted && viewW && viewH) {
    fitted = true;
    fitView();
  }
  render();
}

new ResizeObserver(resize).observe(wrap);
window.addEventListener('resize', resize); // catches devicePixelRatio changes

// Clicked buttons keep focus, which would make a later Space press (pan) or
// Enter re-trigger them. Blur any button as soon as it's clicked.
document.addEventListener('click', (e) => {
  const b = e.target.closest && e.target.closest('button');
  if (b) b.blur();
});

selectColor(state.color);
selectTool('brush');
loadOnionSettings(); // before the first render so ghosts use the stored look
newProject(state.width, state.height);
renderBrushList();
syncBrushUI();
loadStoredBrushes(); // async; re-renders the list when imports arrive

// Headless test hook: test-app.js defines window.__ssmTest to receive the
// pure stroke-math and texture helpers for unit testing. Real browsers
// never set this.
if (typeof window.__ssmTest === 'function') {
  window.__ssmTest({ stampPositions, growRect, clampRect, tipOffsets, textureAlpha, makeRng, smudgeMix,
                     rotVec, boxHandles, pointInBox, boxBounds, scaleBox, resizeCursor });
}

})();
