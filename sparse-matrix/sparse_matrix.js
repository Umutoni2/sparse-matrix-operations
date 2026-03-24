/**
 * ╔══════════════════════════════════════════════════════════════╗
 * ║           S P A R S E   M A T R I X   E N G I N E           ║
 * ║                   DSA Assignment  ·  Node.js                 ║
 * ╠══════════════════════════════════════════════════════════════╣
 * ║  Storage        : Map<number,number>                         ║
 * ║                   key = row * numCols + col  (O(1) access)   ║
 * ║                   Only non-zero entries stored → O(k) memory ║
 * ║  Parser         : single-pass char scanner, no regex         ║
 * ║  Operations     : addition · subtraction · multiplication    ║
 * ║                   "All three" shortcut available             ║
 * ║  No regex · No external libraries · All utilities are custom ║
 * ╚══════════════════════════════════════════════════════════════╝
 *
 * Run:  node sparse_matrix.js
 */

'use strict';

const fs   = require('fs');
const path = require('path');
const rl   = require('readline');

// ═══════════════════════════════════════════════════════════════
//  ANSI TERMINAL COLOURS  (zero dependencies)
// ═══════════════════════════════════════════════════════════════

const T = {
  reset : '\x1b[0m',
  bold  : '\x1b[1m',
  dim   : '\x1b[2m',
  ul    : '\x1b[4m',
  white : '\x1b[97m',  black : '\x1b[30m',
  red   : '\x1b[31m',  green : '\x1b[32m',
  yellow: '\x1b[33m',  cyan  : '\x1b[36m',
  gray  : '\x1b[90m',  bgBlk : '\x1b[40m',
};

/** Wrap string in ANSI codes, always reset at end. */
const $ = (codes, s) => codes + s + T.reset;

// ═══════════════════════════════════════════════════════════════
//  STRING UTILITIES  (no regex, no parseInt / Number())
// ═══════════════════════════════════════════════════════════════

/**
 * Trim spaces, tabs, and carriage-returns from both ends.
 * Handles Windows CRLF files transparently.
 */
function trim(s) {
  let lo = 0, hi = s.length - 1;
  while (lo <= hi && (s[lo] === ' ' || s[lo] === '\t' || s[lo] === '\r')) lo++;
  while (hi >= lo && (s[hi] === ' ' || s[hi] === '\t' || s[hi] === '\r')) hi--;
  return s.slice(lo, hi + 1);
}

/**
 * Convert a validated integer string to a number.
 * Handles optional leading +/-.  Does NOT call Number() or parseInt().
 */
function toInt(s) {
  let sign = 1, i = 0;
  if (s[0] === '-') { sign = -1; i = 1; }
  else if (s[0] === '+') i = 1;
  let v = 0;
  for (; i < s.length; i++) v = v * 10 + (s.charCodeAt(i) - 48);
  return sign * v;
}

/** Format milliseconds as "1.23s" or "456ms". */
function fmtMs(ms) {
  return ms >= 1000 ? (ms / 1000).toFixed(2) + 's' : ms + 'ms';
}

/** Add comma separators to a large integer string  (e.g. 1234567 → "1,234,567"). */
function fmtN(n) {
  const s = String(n);
  let out = '', cnt = 0;
  for (let i = s.length - 1; i >= 0; i--) {
    out = s[i] + out;
    if (++cnt % 3 === 0 && i > 0) out = ',' + out;
  }
  return out;
}

// ═══════════════════════════════════════════════════════════════
//  SPARSE MATRIX CLASS
// ═══════════════════════════════════════════════════════════════

class SparseMatrix {

  /**
   * Two constructors:
   *   new SparseMatrix(fileContentString)  — parse from file text
   *   new SparseMatrix(numRows, numCols)   — allocate blank matrix
   *
   * Internal storage:  Map<key, value>
   *   key = row * numCols + col    (unique 1-D encoding, O(1) hash)
   *   Absent keys are implicitly zero — saves memory for sparse data.
   */
  constructor(rowsOrText, numCols) {
    this._data   = new Map();
    this.numRows = 0;
    this.numCols = 0;

    if (typeof rowsOrText === 'string') {
      this._parse(rowsOrText);
    } else {
      this.numRows = rowsOrText;
      this.numCols = numCols;
    }
  }

  // ── Static file loader ──────────────────────────────────────

  /**
   * Load a SparseMatrix from a file path.
   * Handles: surrounding quotes (PowerShell), UTF-8 BOM, CRLF line-endings.
   */
  static fromFile(filePath) {
    filePath = trim(filePath);
    // Strip surrounding quotes added by some shells / copy-paste
    if (filePath.length > 1 &&
        ((filePath[0] === '"'  && filePath[filePath.length - 1] === '"') ||
         (filePath[0] === "'"  && filePath[filePath.length - 1] === "'")))
      filePath = filePath.slice(1, -1);

    if (!fs.existsSync(filePath))
      throw new Error('File not found: ' + filePath);

    let text = fs.readFileSync(filePath, 'utf8');
    // Strip UTF-8 BOM that Notepad / some editors add
    if (text.charCodeAt(0) === 0xFEFF) text = text.slice(1);

    return new SparseMatrix(text);
  }

  // ── Element access ──────────────────────────────────────────

  /**
   * Return the value at (r, c).
   * Returns 0 for any position not explicitly stored (implicit zero).
   */
  getElement(r, c) {
    const v = this._data.get(r * this.numCols + c);
    return v === undefined ? 0 : v;
  }

  /**
   * Set the value at (r, c).
   * Storing 0 deletes the key, keeping the Map compact.
   */
  setElement(r, c, value) {
    const k = r * this.numCols + c;
    if (value === 0) this._data.delete(k);
    else             this._data.set(k, value);
  }

  /** Number of non-zero entries currently stored. */
  nnz() { return this._data.size; }

  // ── High-speed single-pass file parser ─────────────────────

  /**
   * Parse matrix text in a single character scan.
   * Avoids split() / regex — significantly faster on large files.
   *
   * Expected format:
   *   rows=<N>
   *   cols=<M>
   *   (row, col, value)    ← repeated; blank lines ignored
   *
   * Throws: Error('Input file has wrong format') for any violation.
   */
  _parse(text) {
    let i = 0;
    const len = text.length;

    /* ── rows=N ────────────────────────────────────────────── */
    // Strip UTF-8 BOM (0xFEFF) if present at start of string
    if (i < len && text.charCodeAt(i) === 0xFEFF) i++;
    while (i < len && (text[i] === ' ' || text[i] === '\t' || text[i] === '\r')) i++;
    if (!_expect(text, i, 'rows=')) throw new Error('Input file has wrong format');
    i += 5;
    let numRows = 0, ok = false;
    while (i < len && text[i] !== '\n' && text[i] !== '\r') {
      const c = text.charCodeAt(i);
      if (c >= 48 && c <= 57) { numRows = numRows * 10 + (c - 48); ok = true; i++; }
      else if (text[i] === ' ' || text[i] === '\t') i++;   // allow trailing spaces
      else throw new Error('Input file has wrong format');
    }
    if (!ok) throw new Error('Input file has wrong format');
    while (i < len && (text[i] === '\r' || text[i] === '\n')) i++;
    this.numRows = numRows;

    /* ── cols=N ────────────────────────────────────────────── */
    while (i < len && (text[i] === ' ' || text[i] === '\t' || text[i] === '\r')) i++;
    if (!_expect(text, i, 'cols=')) throw new Error('Input file has wrong format');
    i += 5;
    let numCols = 0; ok = false;
    while (i < len && text[i] !== '\n' && text[i] !== '\r') {
      const c = text.charCodeAt(i);
      if (c >= 48 && c <= 57) { numCols = numCols * 10 + (c - 48); ok = true; i++; }
      else if (text[i] === ' ' || text[i] === '\t') i++;
      else throw new Error('Input file has wrong format');
    }
    if (!ok) throw new Error('Input file has wrong format');
    while (i < len && (text[i] === '\r' || text[i] === '\n')) i++;
    this.numCols = numCols;

    /* ── Entries  (row, col, val) ──────────────────────────── */
    while (i < len) {
      // Skip blank or whitespace-only lines
      while (i < len && (text[i] === ' ' || text[i] === '\t' || text[i] === '\r')) i++;
      if (i >= len) break;
      if (text[i] === '\n') { i++; continue; }

      // Each data line must begin with '('
      if (text[i] !== '(') throw new Error('Input file has wrong format');
      i++;

      // ── row index ────────────────────────────────────────
      while (i < len && (text[i] === ' ' || text[i] === '\t')) i++;
      let row = 0; ok = false;
      while (i < len && text[i] >= '0' && text[i] <= '9') {
        row = row * 10 + (text.charCodeAt(i) - 48); i++; ok = true;
      }
      if (!ok) throw new Error('Input file has wrong format');
      while (i < len && (text[i] === ' ' || text[i] === '\t')) i++;
      if (text[i] !== ',') throw new Error('Input file has wrong format');
      i++;

      // ── col index ────────────────────────────────────────
      while (i < len && (text[i] === ' ' || text[i] === '\t')) i++;
      let col = 0; ok = false;
      while (i < len && text[i] >= '0' && text[i] <= '9') {
        col = col * 10 + (text.charCodeAt(i) - 48); i++; ok = true;
      }
      if (!ok) throw new Error('Input file has wrong format');
      while (i < len && (text[i] === ' ' || text[i] === '\t')) i++;
      if (text[i] !== ',') throw new Error('Input file has wrong format');
      i++;

      // ── value  (may be negative) ──────────────────────────
      while (i < len && (text[i] === ' ' || text[i] === '\t')) i++;
      let neg = false;
      if      (text[i] === '-') { neg = true; i++; }
      else if (text[i] === '+')              i++;
      let val = 0; ok = false;
      while (i < len && text[i] >= '0' && text[i] <= '9') {
        val = val * 10 + (text.charCodeAt(i) - 48); i++; ok = true;
      }
      if (!ok) throw new Error('Input file has wrong format');

      // Reject floating-point values — next char must not be '.' / 'e'
      while (i < len && (text[i] === ' ' || text[i] === '\t')) i++;
      if (text[i] === '.' || text[i] === 'e' || text[i] === 'E')
        throw new Error('Input file has wrong format');

      // Closing parenthesis
      if (text[i] !== ')') throw new Error('Input file has wrong format');
      i++;

      if (neg) val = -val;

      this._data.set(row * numCols + col, val);

      // Advance to the next line
      while (i < len && text[i] !== '\n') i++;
      i++;
    }
  }

  // ── Serialise result to file ────────────────────────────────

  /**
   * Write this matrix to outPath in the standard format.
   * Uses streaming chunk writes (128 KB) to avoid building one huge string.
   */
  toFile(outPath) {
    const fd    = fs.openSync(outPath, 'w');
    const FLUSH = 131072;                    // flush every 128 KB
    let   buf   = 'rows=' + this.numRows + '\ncols=' + this.numCols + '\n';

    for (const [k, v] of this._data) {
      const r = Math.floor(k / this.numCols);
      const c = k % this.numCols;
      buf += '(' + r + ', ' + c + ', ' + v + ')\n';
      if (buf.length >= FLUSH) { fs.writeSync(fd, buf); buf = ''; }
    }
    if (buf) fs.writeSync(fd, buf);
    fs.closeSync(fd);
  }

  // ═══════════════════════════════════════════════════════════
  //  MATRIX OPERATIONS
  // ═══════════════════════════════════════════════════════════

  /**
   * Addition: R = A + B
   * Both matrices must have the same dimensions.
   *
   * Algorithm:
   *   1. Copy all of A into R.                            O(k_A)
   *   2. For each entry in B: add to existing key in R.  O(k_B)
   *   Entries that sum to zero are deleted (stay sparse).
   * Total: O(k_A + k_B)
   */
  static add(A, B) {
    if (A.numRows !== B.numRows || A.numCols !== B.numCols)
      throw new Error(
        'Addition requires equal dimensions. ' +
        'A=' + A.numRows + '×' + A.numCols +
        ', B=' + B.numRows + '×' + B.numCols);

    const R = new SparseMatrix(A.numRows, A.numCols);
    for (const [k, v] of A._data) R._data.set(k, v);
    for (const [k, v] of B._data) {
      const cur = R._data.get(k) || 0;
      const val = cur + v;
      if (val === 0) R._data.delete(k); else R._data.set(k, val);
    }
    return R;
  }

  /**
   * Subtraction: R = A − B
   * Both matrices must have the same dimensions.
   * Same algorithm as addition, using subtraction in the merge step.
   * Total: O(k_A + k_B)
   */
  static sub(A, B) {
    if (A.numRows !== B.numRows || A.numCols !== B.numCols)
      throw new Error(
        'Subtraction requires equal dimensions. ' +
        'A=' + A.numRows + '×' + A.numCols +
        ', B=' + B.numRows + '×' + B.numCols);

    const R = new SparseMatrix(A.numRows, A.numCols);
    for (const [k, v] of A._data) R._data.set(k, v);
    for (const [k, v] of B._data) {
      const cur = R._data.get(k) || 0;
      const val = cur - v;
      if (val === 0) R._data.delete(k); else R._data.set(k, val);
    }
    return R;
  }

  /**
   * Multiplication: R = A × B
   * Requires A.numCols === B.numRows.
   *
   * Algorithm: row-indexed sparse multiply.
   *   1. Build rowA[r] and rowB[r] as FLAT interleaved arrays [c0,v0, c1,v1, …].
   *      Flat arrays have better CPU cache locality than arrays of objects.
   *   2. For each non-zero A[ar, ac] look up the matching row rowB[ac]
   *      and accumulate:  R[ar, bc] += A[ar,ac] × B[ac, bc].
   *
   * Time:  O(k_B) to build index  +  O(k_A × avg_nnz_per_row_of_B) to multiply.
   * For sparse matrices this is vastly faster than dense O(rows × cols × inner).
   */
  static mul(A, B) {
    if (A.numCols !== B.numRows)
      throw new Error(
        'Multiplication requires A.cols = B.rows. ' +
        'A.cols=' + A.numCols + ', B.rows=' + B.numRows);

    const R   = new SparseMatrix(A.numRows, B.numCols);
    const Rnc = B.numCols;

    // Build flat row-index for B: rowB[r] = [c0,v0, c1,v1, …]
    const rowB = new Array(B.numRows);
    for (const [k, v] of B._data) {
      const r = Math.floor(k / B.numCols);
      const c = k % B.numCols;
      if (!rowB[r]) rowB[r] = [];
      rowB[r].push(c, v);     // flat interleaved — avoids object allocation per entry
    }

    // Build flat row-index for A as well
    const rowA = new Array(A.numRows);
    for (const [k, v] of A._data) {
      const r = Math.floor(k / A.numCols);
      const c = k % A.numCols;
      if (!rowA[r]) rowA[r] = [];
      rowA[r].push(c, v);
    }

    // Multiply row by row
    for (let ar = 0; ar < A.numRows; ar++) {
      const aRow = rowA[ar];
      if (!aRow) continue;                      // empty row in A — skip

      for (let ai = 0; ai < aRow.length; ai += 2) {
        const ac   = aRow[ai];                  // A's column (= B's row)
        const av   = aRow[ai + 1];
        const bRow = rowB[ac];
        if (!bRow) continue;                    // no non-zeros in that row of B

        for (let bi = 0; bi < bRow.length; bi += 2) {
          const bc  = bRow[bi];
          const bv  = bRow[bi + 1];
          const rk  = ar * Rnc + bc;
          const cur = R._data.get(rk) || 0;
          const val = cur + av * bv;
          if (val === 0) R._data.delete(rk); else R._data.set(rk, val);
        }
      }
    }
    return R;
  }
}

// ═══════════════════════════════════════════════════════════════
//  PARSER HELPER  (module-level, used inside _parse)
// ═══════════════════════════════════════════════════════════════

/** Check text[pos…pos+s.length-1] === s without allocating a substring. */
function _expect(text, pos, s) {
  if (pos + s.length > text.length) return false;
  for (let j = 0; j < s.length; j++)
    if (text[pos + j] !== s[j]) return false;
  return true;
}

// ═══════════════════════════════════════════════════════════════
//  CLI — BOX-DRAWING COMPONENTS
// ═══════════════════════════════════════════════════════════════

const W = 62;   // total box width

/** Repeat a character n times (no Array.fill). */
function rep(ch, n) { let s = ''; for (let i = 0; i < n; i++) s += ch; return s; }

/** Full-width horizontal rule, e.g.  ╠══════╣ */
function hRule(left, right) {
  return $(T.cyan, left + rep('═', W - 2) + right);
}

/** A box row with left/right borders and padded content. */
function row(content) {
  // content may contain invisible ANSI bytes; pad to visual width
  const visible = content.replace(/\x1b\[[0-9;]*m/g, '');
  const pad2 = W - 2 - visible.length;
  return $(T.cyan, '║') + content + rep(' ', pad2 < 0 ? 0 : pad2) + $(T.cyan, '║');
}

/** Section divider with an inline label. */
function divider(label) {
  const inner = '  ' + label + '  ';
  const fill  = rep('─', W - 2 - inner.length);
  console.log('');
  console.log($(T.cyan + T.dim, '  ╭' + inner + fill + '╮'));
}

/** Print the top splash banner. */
function banner() {
  console.log('');
  console.log(hRule('╔', '╗'));
  console.log(row(''));
  console.log(row('  ' + $(T.bold + T.white, 'SPARSE MATRIX ENGINE')));
  console.log(row(''));
  console.log(hRule('╚', '╝'));
  console.log('');
}

/** Print a load-success line inside the Load Matrices section. */
function printLoaded(label, mat, ms) {
  const dims = mat.numRows + '×' + mat.numCols;
  const nnz  = fmtN(mat.nnz()) + ' nnz';
  const time = fmtMs(ms);
  console.log(
    '  ' + $(T.cyan + T.dim, '│') + '  ' +
    $(T.green + T.bold, '✔ ') + $(T.bold + T.white, label.padEnd(10)) +
    $(T.cyan, dims.padEnd(14)) +
    $(T.yellow, nnz.padEnd(20)) +
    $(T.dim, time));
}

/** Print a result line after an operation completes. */
function printResult(op, result, calcMs, saveMs, outPath) {
  const dims = result.numRows + '×' + result.numCols;
  const nnz  = fmtN(result.nnz()) + ' nnz';
  console.log(
    '  ' + $(T.cyan + T.dim, '│') + '  ' +
    $(T.green + T.bold, '✔ ') + $(T.bold + T.yellow, (op + ':').padEnd(16)) +
    $(T.white, dims.padEnd(14)) +
    $(T.yellow, nnz.padEnd(22)) +
    $(T.dim, 'calc=' + fmtMs(calcMs) + '  save=' + fmtMs(saveMs)));
  console.log(
    '  ' + $(T.cyan + T.dim, '│') + '    ' +
    $(T.dim, '→ ') + $(T.ul + T.white, path.resolve(outPath)));
}

/** Print an error line. */
function errLine(msg) {
  console.log(
    '  ' + $(T.cyan + T.dim, '│') + '  ' +
    $(T.red + T.bold, '✘ ') + $(T.red, msg));
}

// ═══════════════════════════════════════════════════════════════
//  CLI — PROMPT HELPERS
// ═══════════════════════════════════════════════════════════════

/** Promisify readline question. */
function ask(iface, prompt) {
  return new Promise(resolve => iface.question(prompt, resolve));
}

/** Shared prompt prefix. */
const P = () => '  ' + $(T.cyan + T.dim, '│') + '  ' + $(T.bold, '› ');

/** Prompt for a matrix file; retry until valid. */
async function loadMatrix(iface, label) {
  while (true) {
    const raw = trim(await ask(iface, P() + $(T.white, 'Path to ' + label + ': ')));

    // Strip surrounding quotes (PowerShell sometimes wraps paths)
    let p = raw;
    if (p.length > 1 &&
        ((p[0] === '"' && p[p.length-1] === '"') ||
         (p[0] === "'" && p[p.length-1] === "'")))
      p = p.slice(1, -1);

    if (!p.length) { errLine('Path cannot be empty.'); continue; }

    try {
      const t0  = Date.now();
      const mat = SparseMatrix.fromFile(p);
      printLoaded(label, mat, Date.now() - t0);
      return mat;
    } catch (e) {
      errLine(e.message);
    }
  }
}

/** Display operation menu and return the chosen operation descriptor. */
async function pickOp(iface) {
  const ops = [
    { key:'1', sym:'+', name:'Addition',        tag:'A + B', fn: SparseMatrix.add },
    { key:'2', sym:'−', name:'Subtraction',     tag:'A − B', fn: SparseMatrix.sub },
    { key:'3', sym:'×', name:'Multiplication',  tag:'A × B', fn: SparseMatrix.mul },
    { key:'4', sym:'∀', name:'All three',       tag:'+ − ×', fn: null             },
  ];

  divider('SELECT OPERATION');
  for (const op of ops) {
    console.log(
      '  ' + $(T.cyan + T.dim, '│') + '  ' +
      $(T.bgBlk + T.cyan + T.bold, ' ' + op.key + ' ') + '  ' +
      $(T.bold + T.yellow, op.sym.padEnd(4)) +
      $(T.bold + T.white, op.name.padEnd(18)) +
      $(T.dim, op.tag));
  }
  console.log('  ' + $(T.cyan + T.dim, '│'));

  while (true) {
    const raw = trim(await ask(iface, P() + $(T.white, 'Choice [1–4]: ')));
    const found = ops.find(o => o.key === raw);
    if (found) return found;
    errLine('Please enter 1, 2, 3, or 4.');
  }
}

/** Ask for an output file path with a default suggestion. */
async function askOut(iface, defaultName) {
  const raw = trim(await ask(iface,
    P() + $(T.white, 'Output file ') + $(T.dim, '[' + defaultName + ']: ')));
  return raw.length ? raw : defaultName;
}

// ═══════════════════════════════════════════════════════════════
//  OPERATION RUNNER
// ═══════════════════════════════════════════════════════════════

/**
 * Execute one operation: validate dimensions, compute, save, print summary.
 * Dimension errors are caught and displayed without crashing the program.
 */
async function runOp(iface, op, matA, matB) {
  // Dimension pre-check with a clear message before prompting for output path
  if (op.key === '1' || op.key === '2') {
    if (matA.numRows !== matB.numRows || matA.numCols !== matB.numCols) {
      errLine(op.name + ' requires equal dims. A=' + matA.numRows + '×' + matA.numCols +
              ' vs B=' + matB.numRows + '×' + matB.numCols);
      return;
    }
  } else {
    if (matA.numCols !== matB.numRows) {
      errLine('Multiplication: A.cols (' + matA.numCols + ') ≠ B.rows (' + matB.numRows + ')');
      return;
    }
  }

  // Prompt for output destination
  const defaultOut = op.name.toLowerCase().replace(/ /g, '_') + '_result.txt';
  const outPath    = await askOut(iface, defaultOut);

  // Compute
  process.stdout.write(
    '  ' + $(T.cyan + T.dim, '│') + '  ' +
    $(T.dim, 'Computing ' + op.tag + ' …'));
  const t0 = Date.now();
  let result;
  try {
    result = op.fn(matA, matB);
  } catch (e) {
    process.stdout.write('\n');
    errLine(e.message);
    return;
  }
  const calcMs = Date.now() - t0;

  // Save
  process.stdout.write('\r' + rep(' ', 70) + '\r');   // clear the "Computing" line
  const t1 = Date.now();
  result.toFile(outPath);
  const saveMs = Date.now() - t1;

  printResult(op.name, result, calcMs, saveMs, outPath);
}

// ═══════════════════════════════════════════════════════════════
//  MAIN  —  top-level async flow
// ═══════════════════════════════════════════════════════════════

async function main() {
  banner();

  const iface = rl.createInterface({ input: process.stdin, output: process.stdout });

  // Re-run loop: keep same matrices, allow multiple operations
  let matA, matB;

  try {
    // ── 1. Load matrices ─────────────────────────────────────
    divider('LOAD MATRICES');
    matA = await loadMatrix(iface, 'Matrix A');
    matB = await loadMatrix(iface, 'Matrix B');

    while (true) {
      // ── 2. Pick operation ───────────────────────────────────
      const op = await pickOp(iface);

      // ── 3. Run ──────────────────────────────────────────────
      divider('RESULTS');

      if (op.key === '4') {
        // "All three" — run each operation in sequence
        const all = [
          { key:'1', sym:'+', name:'Addition',       tag:'A + B', fn: SparseMatrix.add },
          { key:'2', sym:'−', name:'Subtraction',    tag:'A − B', fn: SparseMatrix.sub },
          { key:'3', sym:'×', name:'Multiplication', tag:'A × B', fn: SparseMatrix.mul },
        ];
        for (const o of all) await runOp(iface, o, matA, matB);
      } else {
        await runOp(iface, op, matA, matB);
      }

      // ── 4. Continue with same matrices? ─────────────────────
      console.log('');
      const again = trim(await ask(iface,
        '  ' + $(T.cyan + T.dim, '│') + '  ' +
        $(T.bold, 'Run another operation with the same matrices? ') +
        $(T.dim, '[y/n]: ')));
      if (again !== 'y' && again !== 'Y') break;
    }

    console.log('');
    console.log('  ' + $(T.dim, 'All done. Goodbye.'));
    console.log('');

  } catch (e) {
    console.log('\n  ' + $(T.red + T.bold, 'Fatal: ') + e.message + '\n');
    iface.close();
    process.exit(1);
  }

  iface.close();
}

main();
