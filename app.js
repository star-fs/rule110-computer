// Rule 110 Computer
//
// Every logic gate is one Rule 110 cell update. Rule 110's local rule is
// f(l,c,r) = l ? (c XOR r) : (c OR r), so a triple of cells whose layout places a
// constant in the right slot turns the centre cell's next state into a gate:
//   [a, 1, b] -> NAND(a, b)      [0, a, b] -> OR(a, b)
//   [1, a, b] -> XOR(a, b)       [0, a, 0] -> a            (wire / buffer)
// A circuit is levelized into layers; each layer is one row of triples, advanced one
// generation by a plain Rule 110 step over the whole row. Between layers the host bus
// only copies bits (wires) and supplies constant rails - it never computes.

const K_CONST = 0, K_IN = 1, K_NAND = 2, K_OR = 3, K_XOR = 4, K_BUF = 5;
const OP_NAME = ['CONST', 'IN', 'NAND', 'OR', 'XOR', 'WIRE'];
const RULE = 110;
const RULE_TABLE = Uint8Array.from({ length: 8 }, (_, i) => (RULE >> i) & 1);
const MAX_ROW = 30000;
const VIEW_CELLS = 600;
const MIN_VIEW_CELLS = 30;
const READ_PULSE_MS = 450;

const PAL = {
    bg: '#020617', alive: '#38bdf8', dead: '#1e293b',
    out: ['#5f1111', '#ff2d2d'], readback: ['#713f12', '#fde047'],
    oper: ['#1e293b', '#38bdf8'], rail: ['#3b2a0a', '#f59e0b'], spill: ['#0b1222', '#334155'],
    res: { [K_NAND]: ['#123524', '#4ade80'], [K_OR]: ['#2a1f4d', '#a78bfa'], [K_XOR]: ['#4a1a36', '#f472b6'], [K_BUF]: ['#0c2433', '#0ea5e9'] },
};

// ---------------------------------------------------------------- circuit builder

function newCircuit() { return { kind: [K_CONST, K_CONST], a: [0, 0], b: [0, 0], label: ['const 0', 'const 1'], inputs: [], memo: new Map(), tag: '' }; }
function addNode(c, k, a, b, label) { c.kind.push(k); c.a.push(a); c.b.push(b); c.label.push(label); return c.kind.length - 1; }
function input(c, label) { const id = addNode(c, K_IN, 0, 0, label); c.inputs.push(id); return id; }
function bitsIn(c, name, n) { return Array.from({ length: n }, (_, i) => input(c, `${name}[${i}]`)); }

function gate(c, k, x, y) {
    if (x > y) { const t = x; x = y; y = t; }
    if (k === K_OR) { if (x === 0 || x === y) return y; if (x === 1) return 1; }
    else if (k === K_XOR) { if (x === 0) return y; if (x === y) return 0; if (x === 1) return gate(c, K_NAND, y, y); }
    else if (k === K_NAND) {
        if (x === 0) return 1;
        if (x === 1) { if (y === 1) return 0; x = y; }
        if (x === y && c.kind[x] === K_NAND && c.a[x] === c.b[x]) return c.a[x];
    }
    const key = `${k}:${x}:${y}`;
    let id = c.memo.get(key);
    if (id === undefined) { id = addNode(c, k, x, y, c.tag); c.memo.set(key, id); }
    return id;
}
const NOT = (c, x) => gate(c, K_NAND, x, x);
const NAND = (c, x, y) => gate(c, K_NAND, x, y);
const AND = (c, x, y) => NOT(c, NAND(c, x, y));
const OR = (c, x, y) => gate(c, K_OR, x, y);
const XOR = (c, x, y) => gate(c, K_XOR, x, y);
const MUX = (c, s, a, b) => NAND(c, NAND(c, NOT(c, s), a), NAND(c, s, b));

function reduceTree(c, xs, f, empty) {
    if (!xs.length) return empty;
    while (xs.length > 1) { const n = []; for (let i = 0; i < xs.length; i += 2) n.push(i + 1 < xs.length ? f(c, xs[i], xs[i + 1]) : xs[i]); xs = n; }
    return xs[0];
}
function fullAdd(c, a, b, cin) { const p = XOR(c, a, b); return [XOR(c, p, cin), NAND(c, NAND(c, a, b), NAND(c, p, cin))]; }
function addBits(c, A, B, cin) { const s = []; for (let i = 0; i < A.length; i++) { const [si, co] = fullAdd(c, A[i], B[i], cin); s.push(si); cin = co; } return [s, cin]; }
function decode2(c, b0, b1) { const n0 = NOT(c, b0), n1 = NOT(c, b1); return [AND(c, n0, n1), AND(c, b0, n1), AND(c, n0, b1), AND(c, b0, b1)]; }
function muxTree(c, sel, items) {
    let xs = items;
    for (let k = 0; xs.length > 1; k++) { const n = []; for (let i = 0; i < xs.length; i += 2) n.push(MUX(c, sel[k], xs[i], xs[i + 1] ?? 0)); xs = n; }
    return xs[0];
}
function multiply(c, a, b) {
    const n = a.length, out = [];
    let S = a.map(x => AND(c, x, b[0])), cy = 0;
    for (let i = 1; i < n; i++) {
        c.tag = `mul row ${i}`;
        out.push(S[0]);
        [S, cy] = addBits(c, [...S.slice(1), cy], a.map(x => AND(c, x, b[i])), 0);
    }
    return [...out, ...S, cy];
}

function evalCircuit(c, inputs, outIds) {
    const v = new Uint8Array(c.kind.length); v[1] = 1;
    c.inputs.forEach((id, k) => v[id] = inputs[k]);
    for (let i = 2; i < v.length; i++) {
        const k = c.kind[i], x = v[c.a[i]], y = v[c.b[i]];
        if (k === K_NAND) v[i] = 1 - (x & y); else if (k === K_OR) v[i] = x | y; else if (k === K_XOR) v[i] = x ^ y;
    }
    return Uint8Array.from(outIds, o => v[o]);
}

// ---------------------------------------------------------------- fabric (Rule 110 layers)

// Layout "compact" (default): each input bit is loaded straight from the host input bus in the layer
// that first uses it, and every gate is placed as late as its consumers allow (same depth D). This
// stops the ROM and register bits from being carried on wires through the early layers, which is
// what made the original layout wide. "original": all inputs enter at layer 1, gates as early as possible.
let fabricLayout = 'compact';

// Width balancing for the compact layout. Working back from the last layer, the signals that need a
// slot in layer L are exactly the gates whose value is still wanted above L: each one is either
// computed in L or carried through L on a wire - one slot either way. Computing a gate swaps its
// slot for slots holding its gate operands one layer down, so width only grows when gates expand.
// A gate is computed when it must be (no earlier layer is possible) or when that does not grow the
// next layer past a cap; the cap giving the narrowest fabric wins. Depth D never changes.
function balanceLevels(c, outIds, live, asap, D) {
    const N = c.kind.length, isGate = i => c.kind[i] >= K_NAND && live[i];
    const uses = new Int32Array(N);
    for (let i = 2; i < N; i++) if (isGate(i)) { if (isGate(c.a[i])) uses[c.a[i]]++; if (isGate(c.b[i]) && c.b[i] !== c.a[i]) uses[c.b[i]]++; }
    const outGates = [...new Set(outIds)].filter(isGate);
    function run(cap) {
        const left = Int32Array.from(uses), lvl = new Int32Array(N), inSet = new Uint8Array(N);
        let active = outGates.slice(), width = 0;
        for (const g of active) inSet[g] = 1;
        for (let L = D; L >= 1; L--) {
            width = Math.max(width, active.length);
            const ready = active.filter(g => left[g] === 0).sort((x, y) => asap[y] - asap[x]);
            let count = active.length;
            const place = new Set();
            const grow = g => [c.a[g], c.b[g]].filter((x, k, arr) => isGate(x) && !inSet[x] && arr.indexOf(x) === k).length;
            for (const g of ready) {
                const d = grow(g) - 1;
                if (asap[g] === L || d <= 0 || count + d <= cap) { place.add(g); count += d; for (const x of [c.a[g], c.b[g]]) if (isGate(x) && !inSet[x]) inSet[x] = 2; }
            }
            const next = [];
            for (const g of active) if (!place.has(g)) next.push(g); else lvl[g] = L;
            for (const g of place) for (const x of new Set([c.a[g], c.b[g]])) if (isGate(x)) { left[x]--; if (inSet[x] === 2) { inSet[x] = 1; next.push(x); } }
            active = next;
        }
        return { width, lvl };
    }
    let best = run(Infinity), lo = 1, hi = best.width;
    while (lo < hi) { const mid = (lo + hi) >> 1, r = run(mid); if (r.width < best.width) best = r; if (r.width <= mid) hi = mid; else lo = mid + 1; }
    for (let i = 2; i < N; i++) if (isGate(i)) asap[i] = best.lvl[i];
}

function scheduleFabric(c, outIds, layout = fabricLayout) {
    const compact = layout === 'compact';
    const N = c.kind.length, level = new Int32Array(N), lastUse = new Int32Array(N), live = new Uint8Array(N);
    const isGate = i => c.kind[i] >= K_NAND;
    for (const o of outIds) live[o] = 1;
    for (let i = N - 1; i >= 2; i--) if (live[i] && isGate(i)) { live[c.a[i]] = 1; live[c.b[i]] = 1; }
    for (let i = 2; i < N; i++) if (live[i] && isGate(i)) level[i] = 1 + Math.max(level[c.a[i]], level[c.b[i]]);
    let D = 1;
    for (const o of outIds) D = Math.max(D, level[o]);
    if (compact) balanceLevels(c, outIds, live, level, D);
    for (let i = 2; i < N; i++) if (live[i] && isGate(i)) { lastUse[c.a[i]] = Math.max(lastUse[c.a[i]], level[i]); lastUse[c.b[i]] = Math.max(lastUse[c.b[i]], level[i]); }
    for (const o of outIds) lastUse[o] = D + 1;
    const inIndex = new Int32Array(N).fill(-1);
    c.inputs.forEach((id, k) => inIndex[id] = k);
    const byLevel = Array.from({ length: D + 1 }, () => []);
    for (let i = 2; i < N; i++) if (live[i] && isGate(i)) byLevel[level[i]].push(i);
    const layers = [], counts = [0, 0, 0, 0, 0, 0], outIndex = new Map();
    outIds.forEach((o, i) => { if (!outIndex.has(o)) outIndex.set(o, []); outIndex.get(o).push(i); });
    let pos = new Int32Array(N).fill(-1), W = 3;
    for (let L = 1; L <= D; L++) {
        const slots = [];
        for (let i = 2; i < N; i++) {
            if (!live[i]) continue;
            const carry = isGate(i) || !compact ? level[i] < L && lastUse[i] > L : L === D && lastUse[i] > D;
            if (carry) slots.push([K_BUF, i]);
        }
        for (const g of byLevel[L]) slots.push([c.kind[g], g]);
        const n = slots.length, src = new Int32Array(3 * n), op = new Uint8Array(n), sig = new Int32Array(n), isOut = new Uint8Array(n), npos = new Int32Array(N).fill(-1);
        const ref = x => {
            if (x < 2) return -1 - x;
            const fromBus = inIndex[x] >= 0 && (compact || L === 1), r = fromBus ? -3 - inIndex[x] : pos[x];
            if (r === -1 || r === -2 || (!fromBus && r < 0)) throw new Error(`scheduler: signal ${x} unavailable at layer ${L}`);
            return r;
        };
        slots.forEach(([k, s], j) => {
            const t = 3 * j;
            op[j] = k; sig[j] = s; npos[s] = t + 1; counts[k]++; isOut[j] = outIndex.has(s) ? 1 : 0;
            if (k === K_BUF) { src[t] = -1; src[t + 1] = ref(s); src[t + 2] = -1; return; }
            const a = ref(c.a[s]), b = ref(c.b[s]);
            if (k === K_NAND) { src[t] = a; src[t + 1] = -2; src[t + 2] = b; }
            else if (k === K_OR) { src[t] = -1; src[t + 1] = a; src[t + 2] = b; }
            else { src[t] = -2; src[t + 1] = a; src[t + 2] = b; }
        });
        pos = npos; W = Math.max(W, 3 * n);
        layers.push({ n, src, op, sig, isOut });
    }
    if (W > MAX_ROW) throw new Error(`fabric row would be ${W} cells wide (limit ${MAX_ROW}) - make the task smaller`);
    const outSrc = Int32Array.from(outIds, o => o < 2 ? -1 - o : pos[o]);
    return { D, W, layers, outSrc, counts, nIn: c.inputs.length, circuit: c, outIds, outIndex, layout };
}

function rule110Step(src, dst, n) {
    for (let i = 0; i < n; i++) dst[i] = RULE_TABLE[((i > 0 ? src[i - 1] : 0) << 2) | (src[i] << 1) | (i + 1 < n ? src[i + 1] : 0)];
}
function runLayer(fab, L, prevEvo, inputs, load, evo) {
    const { src, n } = fab.layers[L];
    for (let j = 0; j < 3 * n; j++) { const s = src[j]; load[j] = s >= 0 ? prevEvo[s] : s === -1 ? 0 : s === -2 ? 1 : inputs[-3 - s]; }
    rule110Step(load, evo, 3 * n);
}
function allocRows(fab) { return fab.layers.map(l => ({ load: new Uint8Array(3 * l.n), evo: new Uint8Array(3 * l.n) })); }
function readOutputs(fab, evo) { return Uint8Array.from(fab.outSrc, s => s >= 0 ? evo[s] : s === -2 ? 1 : 0); }
function simulateCycle(fab, inputs, rows) {
    let prev = null;
    fab.layers.forEach((_, L) => { runLayer(fab, L, prev, inputs, rows[L].load, rows[L].evo); prev = rows[L].evo; });
    return readOutputs(fab, prev);
}

// ---------------------------------------------------------------- bits helpers

const toBits = (v, n) => Array.from({ length: n }, (_, i) => Math.floor(v / 2 ** i) % 2);
const fromBits = (bits, off, n) => { let v = 0; for (let i = 0; i < n; i++) v += bits[off + i] * 2 ** i; return v; };
const bin = (v, n) => v.toString(2).padStart(n, '0');

// ---------------------------------------------------------------- CPU

// Opcode 8 is the memory instruction: imm bit 7 = store, bit 6 = absolute address, bits 3-0 = offset.
//   LD rd, [rs+k]  rd = RAM[(rs + k) & 15]     ST rd, [rs+k]  RAM[(rs + k) & 15] = rd     [k] = absolute
// (SHL rd is kept as an assembler shorthand for ADD rd, rd, which frees its old opcode.)
const ISA = ['HALT', 'LDI', 'MOV', 'ADD', 'SUB', 'AND', 'OR', 'XOR', 'MEM', 'SHR', 'ADDI', 'JMP', 'JZ', 'JNZ', 'JLT', 'OUT'];
const ARGS = { HALT: '', NOP: '', LDI: 'ri', MOV: 'rr', ADD: 'rr', SUB: 'rr', AND: 'rr', OR: 'rr', XOR: 'rr', SHL: 'r', SHR: 'r', ADDI: 'ri', JMP: 'l', JZ: 'rl', JNZ: 'rl', JLT: 'rrl', OUT: 'r', LD: 'rm', ST: 'rm' };
const ROM_WORDS = 64, PC_BITS = Math.log2(ROM_WORDS), PC_MASK = ROM_WORDS - 1, RAM_BYTES = 16;
// bit offsets of the CPU circuit's state inputs and next-state outputs
const CPU_IN = { R: 0, PC: 32, H: 32 + PC_BITS, ROM: 33 + PC_BITS, RAM: 33 + PC_BITS + 16 * ROM_WORDS };
const CPU_OUT = { R: 0, PC: 32, H: 32 + PC_BITS, OUTV: 33 + PC_BITS, OUT: 34 + PC_BITS, RAM: 42 + PC_BITS };

const PROGRAMS = {
    fib: `; 16-bit Fibonacci on the 8-bit CPU: a = r1:r0 and b = r3:r2 (high:low).
; Each add carries from the low byte into the high byte by hand; old b is
; parked in RAM while b becomes a + b. Stops at the last value under 65536.
; out: u16  (each pair of OUT bytes, high then low, is one 16-bit number)
      LDI r2, 1         ; b = 1   (a = 0)
loop: OUT r1            ; print a
      OUT r0
      ST r2, [0]        ; save b
      ST r3, [1]
      ADD r2, r0        ; b = a + b, low byte
      ADD r3, r1        ; high byte
      LD r0, [0]        ; a = old b, low byte
      JLT r2, r0, carry ; low byte wrapped: carry 1 into the high byte
      JMP high
carry: ADDI r3, 1
high: LD r1, [1]        ; a = old b, high byte
      JLT r3, r1, done  ; new b < a: the sum passed 65535
      JLT r1, r3, loop
      JLT r2, r0, done  ; equal high bytes: compare low bytes
      JMP loop
done: OUT r1            ; print the last one
      OUT r0
      HALT`,
    mul: `; 13 x 11 by shift-and-add
      LDI r0, 13        ; multiplicand
      LDI r1, 11        ; multiplier
      LDI r2, 0         ; product
loop: JZ r1, done
      LDI r3, 1
      AND r3, r1        ; low bit of multiplier
      JZ r3, skip
      ADD r2, r0
skip: SHL r0
      SHR r1
      JMP loop
done: OUT r2
      HALT`,
    gcd: `; Euclid by repeated subtraction
      LDI r0, 84
      LDI r1, 36
loop: JZ r1, done
      JLT r0, r1, swap
      SUB r0, r1
      JMP loop
swap: MOV r2, r0
      MOV r0, r1
      MOV r1, r2
      JMP loop
done: OUT r0
      HALT`,
    primes: `; primes below 40 by trial division
      LDI r0, 2         ; n
next: LDI r1, 2         ; d
test: JLT r1, r0, chk   ; d < n: try d
      OUT r0            ; no divisor found
      JMP inc
chk:  MOV r2, r0
mod:  JLT r2, r1, rem   ; r2 = n mod d
      SUB r2, r1
      JMP mod
rem:  JZ r2, inc        ; divisible: composite
      ADDI r1, 1
      JMP test
inc:  ADDI r0, 1
      LDI r3, 40
      JLT r0, r3, next
      HALT`,
    countdown: `; count down from 10
      LDI r0, 10
loop: OUT r0
      ADDI r0, -1
      JNZ r0, loop
      OUT r0
      HALT`,
    bubble: `; bubble sort of 4 random numbers. The CPU has no RAM, so the "list" is the
; 4 registers; swaps use the XOR trick (no spare register). Passes repeat
; until no neighbours are out of order. Prints the list, then the sorted list.
      LDI r0, $RAND
      LDI r1, $RAND
      LDI r2, $RAND
      LDI r3, $RAND
      OUT r0
      OUT r1
      OUT r2
      OUT r3
pass: JLT r0, r1, s1    ; in order: skip the swap
      XOR r0, r1
      XOR r1, r0
      XOR r0, r1
s1:   JLT r1, r2, s2
      XOR r1, r2
      XOR r2, r1
      XOR r1, r2
s2:   JLT r2, r3, s3
      XOR r2, r3
      XOR r3, r2
      XOR r2, r3
s3:   JLT r1, r0, pass  ; any inversion left: another pass
      JLT r2, r1, pass
      JLT r3, r2, pass
      OUT r0
      OUT r1
      OUT r2
      OUT r3
      HALT`,
    sincos: `; sine and cosine by Minsky's circle algorithm (HAKMEM item 149):
;   cos -= sin/8;  sin += cos/8   - only shifts and adds, no multiply
; Values are stored as 128 + v (so 128 is zero); then SHR + ADDI 64 is
; a signed (arithmetic) shift. Two turns of radius 60.
; plot: sin, cos
      LDI r0, 188       ; cos = +60
      LDI r1, 128       ; sin = 0
      LDI r3, 100       ; steps
loop: OUT r1
      OUT r0
      MOV r2, r1        ; t = sin / 8
      SHR r2
      ADDI r2, 64
      SHR r2
      ADDI r2, 64
      SHR r2
      ADDI r2, 64
      SUB r0, r2        ; cos -= t
      ADDI r0, 128
      MOV r2, r0        ; t = cos / 8
      SHR r2
      ADDI r2, 64
      SHR r2
      ADDI r2, 64
      SHR r2
      ADDI r2, 64
      ADD r1, r2        ; sin += t
      ADDI r1, 128
      ADDI r3, -1
      JNZ r3, loop
      HALT`,
    lcg: `; pseudo-random numbers: x = 5x + 17 (mod 256), a full-period linear
; congruential generator. 5x is done as (x << 2) + x.
      LDI r0, $RAND     ; seed
      LDI r3, 40        ; how many
loop: MOV r1, r0
      SHL r1
      SHL r1            ; r1 = 4x
      ADD r0, r1        ; x = 5x
      ADDI r0, 17
      OUT r0
      ADDI r3, -1
      JNZ r3, loop
      HALT`,
    sort8: `; bubble sort of 8 random numbers in RAM[0..7], using LD/ST [r+k]
      .data $RAND, $RAND, $RAND, $RAND, $RAND, $RAND, $RAND, $RAND
      LDI r2, 8
      LDI r0, 0
show: LD r1, [r0]       ; print the list as loaded
      OUT r1
      ADDI r0, 1
      JLT r0, r2, show
      LDI r3, 7         ; compare pairs below index r3
pass: LDI r0, 0         ; i
cmp:  LD r1, [r0]       ; x = a[i]
      LD r2, [r0+1]     ; y = a[i+1]
      JLT r1, r2, next  ; already in order
      ST r2, [r0]       ; swap
      ST r1, [r0+1]
next: ADDI r0, 1
      JLT r0, r3, cmp
      ADDI r3, -1       ; the largest has bubbled to the top
      JNZ r3, pass
      LDI r2, 8
      LDI r0, 0
done: LD r1, [r0]       ; print the sorted list
      OUT r1
      ADDI r0, 1
      JLT r0, r2, done
      HALT`,
    sum: `; sum of an array: .data preloads RAM, LD [r0] walks it
      .data 12, 7, 30, 1, 22, 9, 15, 4
      LDI r0, 0         ; index
      LDI r1, 0         ; sum
      LDI r2, 8         ; length
loop: LD r3, [r0]
      ADD r1, r3
      ADDI r0, 1
      JLT r0, r2, loop
      OUT r1            ; 100
      HALT`,
};

function assemble(src) {
    const items = [], labels = {}, ram = new Uint8Array(RAM_BYTES);
    let nData = 0;
    src.split('\n').forEach((raw, ln) => {
        let s = raw.replace(/[;#].*/, '').trim(), m;
        while ((m = s.match(/^([A-Za-z_]\w*):\s*/))) { labels[m[1].toLowerCase()] = items.length; s = s.slice(m[0].length); }
        if (!s) return;
        if ((m = /^\.data\b(.*)$/i.exec(s))) {
            for (const t of m[1].split(',').map(x => x.trim()).filter(Boolean)) {
                const v = Number(t);
                if (!Number.isInteger(v) || v < -128 || v > 255) throw new Error(`line ${ln + 1}: bad .data value '${t}'`);
                if (nData >= RAM_BYTES) throw new Error(`line ${ln + 1}: .data fills more than the ${RAM_BYTES} bytes of RAM`);
                ram[nData++] = v & 255;
            }
            return;
        }
        const [mn, ...rest] = s.split(/\s+/);
        items.push({ mn: mn.toUpperCase(), args: rest.join(' ').split(',').map(t => t.trim()).filter(Boolean), ln: ln + 1 });
    });
    if (!items.length) throw new Error('program is empty');
    if (items.length > ROM_WORDS) throw new Error(`program has ${items.length} instructions; the ROM holds ${ROM_WORDS}`);
    const rom = new Uint16Array(ROM_WORDS);
    items.forEach(({ mn, args, ln }, addr) => {
        const spec = ARGS[mn];
        if (spec === undefined) throw new Error(`line ${ln}: unknown instruction '${mn}'`);
        if (args.length !== spec.length) throw new Error(`line ${ln}: ${mn} takes ${spec.length} operand(s), got ${args.length}`);
        const reg = t => { const m = /^r([0-3])$/i.exec(t); if (!m) throw new Error(`line ${ln}: expected r0-r3, got '${t}'`); return +m[1]; };
        const num = t => { const v = Number(t); if (!Number.isInteger(v) || v < -128 || v > 255) throw new Error(`line ${ln}: bad immediate '${t}'`); return v & 255; };
        const lab = t => { const k = t.toLowerCase(); if (k in labels) return labels[k]; const v = Number(t); if (Number.isInteger(v) && v >= 0 && v < ROM_WORDS) return v; throw new Error(`line ${ln}: unknown label '${t}'`); };
        const mem = t => {
            const m = /^\[\s*(?:r([0-3])\s*(?:\+\s*(\w+))?|(\w+))\s*\]$/i.exec(t);
            if (!m) throw new Error(`line ${ln}: expected a memory operand like [r1], [r1+3] or [5], got '${t}'`);
            const off = Number(m[2] ?? m[3] ?? 0);
            if (!Number.isInteger(off) || off < 0 || off > 15) throw new Error(`line ${ln}: memory offset must be 0-15, got '${m[2] ?? m[3]}'`);
            return { base: m[1] === undefined ? null : +m[1], off };
        };
        let rd = 0, rs = 0, imm = 0, nr = 0, op = mn === 'NOP' ? 2 : mn === 'SHL' ? 3 : mn === 'LD' || mn === 'ST' ? 8 : ISA.indexOf(mn);
        [...spec].forEach((ch, i) => {
            const t = args[i];
            if (ch === 'r') { if (nr++ === 0) rd = reg(t); else rs = reg(t); }
            else if (ch === 'i') imm = num(t);
            else if (ch === 'm') { const a = mem(t); rs = a.base ?? 0; imm = (mn === 'ST' ? 128 : 0) | (a.base === null ? 64 : 0) | a.off; }
            else imm = lab(t);
        });
        if (mn === 'SHL') rs = rd;
        rom[addr] = (op << 12) | (rd << 10) | (rs << 8) | imm;
    });
    return { rom, ram, size: items.length };
}

function disasm(w) {
    const op = w >> 12, rd = `r${(w >> 10) & 3}`, rs = `r${(w >> 8) & 3}`, imm = w & 255;
    if (op === 8) { const off = imm & 15; return `${imm & 128 ? 'ST' : 'LD'} ${rd}, [${imm & 64 ? off : rs + (off ? '+' + off : '')}]`; }
    const m = ISA[op], j = imm & PC_MASK;
    const a = { '': [], ri: [rd, imm], rr: [rd, rs], r: [rd], l: [j], rl: [rd, j], rrl: [rd, rs, j] }[ARGS[m]];
    return `${m} ${a.join(', ')}`.trim();
}

function cpuRef(s, rom) {
    const n = { R: s.R.slice(), pc: s.pc, halted: s.halted, outv: 0, out: 0, ram: s.ram.slice() };
    if (s.halted) return n;
    const w = rom[s.pc], op = w >> 12, rd = (w >> 10) & 3, rs = (w >> 8) & 3, imm = w & 255, A = s.R[rd], B = s.R[rs];
    let pc = (s.pc + 1) & PC_MASK, wr = null;
    switch (op) {
        case 0: n.halted = 1; pc = s.pc; break;
        case 1: wr = imm; break;
        case 2: wr = B; break;
        case 3: wr = (A + B) & 255; break;
        case 4: wr = (A - B) & 255; break;
        case 5: wr = A & B; break;
        case 6: wr = A | B; break;
        case 7: wr = A ^ B; break;
        case 8: { const addr = imm & 64 ? imm & 15 : (B + (imm & 15)) & 15; if (imm & 128) n.ram[addr] = A; else wr = s.ram[addr]; break; }
        case 9: wr = A >> 1; break;
        case 10: wr = (A + imm) & 255; break;
        case 11: pc = imm & PC_MASK; break;
        case 12: if (A === 0) pc = imm & PC_MASK; break;
        case 13: if (A !== 0) pc = imm & PC_MASK; break;
        case 14: if (A < B) pc = imm & PC_MASK; break;
        case 15: n.outv = 1; n.out = A; break;
    }
    if (wr !== null) n.R[rd] = wr;
    n.pc = pc;
    return n;
}

// Next-state function of the whole CPU as one combinational circuit.
// inputs: R0..R3 (4x8), PC, HALT, ROM (words x 16), RAM (16x8)
// outputs: R0'..R3', PC', HALT', OUTV, OUT (= A), RAM' (16x8) - see CPU_IN / CPU_OUT
function buildCPU() {
    const c = newCircuit();
    const R = [0, 1, 2, 3].map(r => bitsIn(c, `R${r}`, 8)), PC = bitsIn(c, 'PC', PC_BITS), H = input(c, 'HALT');
    const ROM = Array.from({ length: ROM_WORDS }, (_, a) => bitsIn(c, `ROM${a}`, 16));
    const RAM = Array.from({ length: RAM_BYTES }, (_, a) => bitsIn(c, `RAM${a}`, 8));
    c.tag = 'fetch (ROM mux by PC)'; const I = Array.from({ length: 16 }, (_, b) => muxTree(c, PC, ROM.map(w => w[b])));
    const imm = I.slice(0, 8), rs = I.slice(8, 10), rd = I.slice(10, 12), op = I.slice(12, 16);
    c.tag = 'decode'; const lo = decode2(c, op[0], op[1]), hi = decode2(c, op[2], op[3]);
    const dec = Array.from({ length: 16 }, (_, k) => AND(c, lo[k & 3], hi[k >> 2]));
    c.tag = 'register read A (rd)'; const A = Array.from({ length: 8 }, (_, b) => muxTree(c, rd, R.map(r => r[b])));
    c.tag = 'register read B (rs)'; const B = Array.from({ length: 8 }, (_, b) => muxTree(c, rs, R.map(r => r[b])));
    c.tag = 'memory address'; const off = imm.slice(0, 4), [based] = addBits(c, B.slice(0, 4), off, 0);
    const addr = based.map((x, b) => MUX(c, imm[6], x, off[b]));
    c.tag = 'memory read'; const mem = Array.from({ length: 8 }, (_, b) => muxTree(c, addr, RAM.map(w => w[b])));
    const isLoad = AND(c, dec[8], NOT(c, imm[7])), isStore = AND(c, dec[8], imm[7]);
    c.tag = 'ALU add'; const [sum] = addBits(c, A, B.map((x, b) => MUX(c, dec[10], x, imm[b])), 0);
    c.tag = 'ALU subtract / compare'; const [diff, carry] = addBits(c, A, B.map(x => NOT(c, x)), 1); const lt = NOT(c, carry);
    c.tag = 'ALU logic'; const andR = A.map((x, b) => AND(c, x, B[b])), orR = A.map((x, b) => OR(c, x, B[b])), xorR = A.map((x, b) => XOR(c, x, B[b]));
    const shr = [...A.slice(1), 0];
    c.tag = 'result select';
    const srcs = [[dec[1], imm], [dec[2], B], [OR(c, dec[3], dec[10]), sum], [dec[4], diff], [dec[5], andR], [dec[6], orR], [dec[7], xorR], [isLoad, mem], [dec[9], shr]];
    const res = Array.from({ length: 8 }, (_, b) => reduceTree(c, srcs.map(([en, v]) => AND(c, en, v[b])), OR, 0));
    const notH = NOT(c, H), we = AND(c, OR(c, reduceTree(c, [1, 2, 3, 4, 5, 6, 7, 9, 10].map(k => dec[k]), OR, 0), isLoad), notH);
    c.tag = 'register write'; const rdDec = decode2(c, rd[0], rd[1]);
    const newR = R.map((reg, r) => { const wr = AND(c, we, rdDec[r]); return reg.map((x, b) => MUX(c, wr, x, res[b])); });
    c.tag = 'memory write'; const stEn = AND(c, isStore, notH), aLo = decode2(c, addr[0], addr[1]), aHi = decode2(c, addr[2], addr[3]);
    const newRAM = RAM.map((w, a) => { const wr = AND(c, stEn, AND(c, aLo[a & 3], aHi[a >> 2])); return w.map((x, b) => MUX(c, wr, x, A[b])); });
    c.tag = 'branch'; const zero = NOT(c, reduceTree(c, A, OR, 0));
    const jump = AND(c, notH, reduceTree(c, [dec[11], AND(c, dec[12], zero), AND(c, dec[13], NOT(c, zero)), AND(c, dec[14], lt)], OR, 0));
    c.tag = 'PC increment'; const inc = []; let cy = 1; for (const p of PC) { inc.push(XOR(c, p, cy)); cy = AND(c, p, cy); }
    c.tag = 'PC select'; const hold = OR(c, H, dec[0]);
    const pcN = PC.map((p, b) => MUX(c, hold, MUX(c, jump, inc[b], imm[b]), p));
    c.tag = 'halt / output'; const outv = AND(c, dec[15], notH);
    return { c, outs: [...newR.flat(), ...pcN, hold, outv, ...A, ...newRAM.flat()] };
}

const cpuFabrics = {};
function makeCpuTask(src, maxCycles) {
    const { rom, ram: ramInit, size } = assemble(src);
    if (!cpuFabrics[fabricLayout]) { const { c, outs } = buildCPU(); cpuFabrics[fabricLayout] = scheduleFabric(c, outs); }
    const cpuFabric = cpuFabrics[fabricLayout];
    const pad = n => String(n).padStart(2, '0');
    const t = {
        type: 'cpu', fab: cpuFabric, rom, ramInit, size, maxCycles,
        title: `CPU · 8-bit · 4 regs · ${RAM_BYTES}-byte RAM · ${ROM_WORDS}-word ROM (${size} used)`,
        begin() { t.s = { R: [0, 0, 0, 0], pc: 0, halted: 0, ram: Array.from(ramInit) }; t.out = []; t.refOk = 0; t.refFail = -1; t.last = null; t.lastStore = -1; },
        cycleInputs() {
            const v = new Uint8Array(t.fab.nIn), s = t.s; let k = 0;
            for (const r of s.R) for (const b of toBits(r, 8)) v[k++] = b;
            for (const b of toBits(s.pc, PC_BITS)) v[k++] = b;
            v[k++] = s.halted;
            for (const w of rom) for (const b of toBits(w, 16)) v[k++] = b;
            for (const x of s.ram) for (const b of toBits(x, 8)) v[k++] = b;
            return v;
        },
        endCycle(o, cycle) {
            const n = {
                R: [0, 1, 2, 3].map(r => fromBits(o, CPU_OUT.R + 8 * r, 8)), pc: fromBits(o, CPU_OUT.PC, PC_BITS), halted: o[CPU_OUT.H],
                outv: o[CPU_OUT.OUTV], out: fromBits(o, CPU_OUT.OUT, 8), ram: Array.from({ length: RAM_BYTES }, (_, a) => fromBits(o, CPU_OUT.RAM + 8 * a, 8)),
            };
            const ref = cpuRef(t.s, rom);
            const same = n.pc === ref.pc && n.halted === ref.halted && n.outv === ref.outv && (!n.outv || n.out === ref.out) && n.R.every((r, i) => r === ref.R[i]) && n.ram.every((x, i) => x === ref.ram[i]);
            if (same) t.refOk++; else if (t.refFail < 0) t.refFail = cycle;
            t.last = { pc: t.s.pc, ins: disasm(rom[t.s.pc]) };
            t.lastStore = n.ram.findIndex((x, i) => x !== t.s.ram[i]);
            if (n.outv) t.out.push(n.out);
            t.s = { R: n.R, pc: n.pc, halted: n.halted, ram: n.ram };
            return !n.halted && cycle + 1 < maxCycles;
        },
        cycleLabel(inputs) { const pc = fromBits(inputs, CPU_IN.PC, PC_BITS); return inputs[CPU_IN.H] ? `pc ${pc} · halted` : `pc ${pad(pc)} · ${disasm(rom[pc])}`; },
        report(st) {
            const s = t.s, lines = [];
            lines.push(`PC ${pad(s.pc)}   ${s.halted ? 'HALTED' : 'next: ' + disasm(rom[s.pc])}`);
            lines.push(s.R.map((r, i) => `r${i}=${String(r).padStart(3)}`).join('  '));
            if (t.last) lines.push(`last: ${t.last.ins}`);
            const cell = i => String(s.ram[i]).padStart(4) + (i === t.lastStore ? '*' : ' ');
            lines.push('', `RAM${t.lastStore >= 0 ? '   (* = last write)' : ''}`);
            for (let row = 0; row < RAM_BYTES; row += 4) lines.push(`[${String(row).padStart(2)}] ${[0, 1, 2, 3].map(k => cell(row + k)).join('')}`);
            if (st.outFormat === 'u16') { const v = pairU16(t.out); lines.push('', `OUT as 16-bit numbers (${v.length}):`, v.length ? v.join(' ') : '—', `(${t.out.length} bytes, high then low)`); }
            else lines.push('', `OUT (${t.out.length}):`, t.out.length ? t.out.join(' ') : '—');
            if (st.done) lines.push('', s.halted ? `halted after ${st.cycle} cycles` : `stopped at max cycles (${maxCycles})`);
            return lines.join('\n');
        },
        refLine() { return t.refFail >= 0 ? `✗ first mismatch at cycle ${t.refFail}` : `✓ ${t.refOk} cycles vs JS CPU emulator`; },
    };
    return t;
}

// ---------------------------------------------------------------- arithmetic

const ARITH = {
    add: { sym: 'A + B', width: n => n + 1, ref: (a, b) => a + b },
    sub: { sym: 'A − B', width: n => n + 1, ref: (a, b, n) => ((a - b + 2 ** n) % 2 ** n) + (a < b ? 2 ** n : 0) },
    mul: { sym: 'A × B', width: n => 2 * n, ref: (a, b) => a * b },
    and: { sym: 'A AND B', width: n => n, ref: (a, b, n) => bitwise(a, b, n, (x, y) => x & y) },
    or: { sym: 'A OR B', width: n => n, ref: (a, b, n) => bitwise(a, b, n, (x, y) => x | y) },
    xor: { sym: 'A XOR B', width: n => n, ref: (a, b, n) => bitwise(a, b, n, (x, y) => x ^ y) },
    lt: { sym: 'A < B', width: () => 1, ref: (a, b) => +(a < b) },
    eq: { sym: 'A == B', width: () => 1, ref: (a, b) => +(a === b) },
    max: { sym: 'max(A, B)', width: n => n, ref: (a, b) => Math.max(a, b) },
};
function bitwise(a, b, n, f) { const x = toBits(a, n), y = toBits(b, n); return fromBits(x.map((v, i) => f(v, y[i])), 0, n); }

function makeArithTask(op, n, A, B) {
    const lim = 2 ** n;
    if (!(Number.isInteger(A) && A >= 0 && A < lim && Number.isInteger(B) && B >= 0 && B < lim)) throw new Error(`A and B must be integers in 0..${lim - 1} for ${n}-bit operands`);
    const c = newCircuit(), a = bitsIn(c, 'A', n), b = bitsIn(c, 'B', n);
    const subtract = () => addBits(c, a, b.map(x => NOT(c, x)), 1);
    let out;
    c.tag = op;
    switch (op) {
        case 'add': { const [s, co] = addBits(c, a, b, 0); out = [...s, co]; break; }
        case 'sub': { const [s, co] = subtract(); out = [...s, NOT(c, co)]; break; }
        case 'mul': out = multiply(c, a, b); break;
        case 'and': out = a.map((x, i) => AND(c, x, b[i])); break;
        case 'or': out = a.map((x, i) => OR(c, x, b[i])); break;
        case 'xor': out = a.map((x, i) => XOR(c, x, b[i])); break;
        case 'lt': out = [NOT(c, subtract()[1])]; break;
        case 'eq': out = [NOT(c, reduceTree(c, a.map((x, i) => XOR(c, x, b[i])), OR, 0))]; break;
        case 'max': { const lt = NOT(c, subtract()[1]); c.tag = 'max select'; out = a.map((x, i) => MUX(c, lt, x, b[i])); break; }
    }
    const spec = ARITH[op], w = spec.width(n), expected = spec.ref(A, B, n);
    const t = {
        type: 'arith', fab: scheduleFabric(c, out), title: `${spec.sym} · ${n}-bit operands → ${w}-bit result`,
        begin() { t.result = null; },
        cycleInputs() { return Uint8Array.from([...toBits(A, n), ...toBits(B, n)]); },
        endCycle(o) { t.result = fromBits(o, 0, w); return false; },
        cycleLabel() { return spec.sym; },
        report() {
            const lines = [`${spec.sym}   (${n}-bit)`, `A = ${String(A).padEnd(6)} 0b${bin(A, n)}`, `B = ${String(B).padEnd(6)} 0b${bin(B, n)}`, ''];
            if (t.result === null) return lines.concat('result: (not computed yet)').join('\n');
            lines.push(`fabric → ${t.result}   0x${t.result.toString(16).toUpperCase()}`, `         0b${bin(t.result, w)}`);
            if (op === 'sub') lines.push(`         (low ${n} bits = ${t.result % lim}, borrow = ${t.result >= lim ? 1 : 0})`);
            lines.push(`JS ref → ${expected}  ${t.result === expected ? '✓' : '✗ MISMATCH'}`);
            return lines.join('\n');
        },
        refLine() { return t.result === null ? '—' : t.result === expected ? '✓ matches JS arithmetic' : '✗ differs from JS arithmetic'; },
    };
    return t;
}

// ---------------------------------------------------------------- boolean expressions

const EXPRS = {
    adder: 'sum  = a ^ b ^ cin\ncout = (a & b) | (cin & (a ^ b))',
    maj: 'maj = (a & b) | (b & c) | (a & c)',
    mux: 'y = (~s & a) | (s & b)',
    parity: 'p = a ^ b ^ c ^ d ^ e',
    demorgan: 'lhs  = ~(a & b)\nrhs  = ~a | ~b\nsame = ~(~(a & b) ^ (~a | ~b))',
};

function parseExprs(src) {
    const vars = new Set(), exprs = [];
    src.split(/[;\n]/).map(s => s.trim()).filter(Boolean).forEach((line, li) => {
        let name = `out${li}`, body = line;
        const m = /^([A-Za-z_]\w*)\s*=(?!=)\s*(.*)$/.exec(line);
        if (m) { name = m[1]; body = m[2]; }
        const toks = body.match(/[A-Za-z_]\w*|[01]|[()&|^~!+*]|\S/g) || [];
        let p = 0;
        const peek = () => toks[p], next = () => toks[p++];
        const fail = msg => { throw new Error(`${name}: ${msg}`); };
        function primary() {
            const tk = next();
            if (tk === undefined) fail('unexpected end of expression');
            if (tk === '(') { const e = orE(); if (next() !== ')') fail("missing ')'"); return e; }
            if (tk === '~' || tk === '!') return { op: 'not', a: primary() };
            if (tk === '0' || tk === '1') return { op: 'const', v: +tk };
            if (/^[A-Za-z_]/.test(tk)) { vars.add(tk); return { op: 'var', name: tk }; }
            fail(`unexpected '${tk}'`);
        }
        function andE() { let e = primary(); while (peek() === '&' || peek() === '*') { next(); e = { op: 'and', a: e, b: primary() }; } return e; }
        function xorE() { let e = andE(); while (peek() === '^') { next(); e = { op: 'xor', a: e, b: andE() }; } return e; }
        function orE() { let e = xorE(); while (peek() === '|' || peek() === '+') { next(); e = { op: 'or', a: e, b: xorE() }; } return e; }
        const ast = orE();
        if (p < toks.length) fail(`unexpected '${toks[p]}'`);
        exprs.push({ name, ast });
    });
    if (!exprs.length) throw new Error('enter at least one expression');
    const vs = [...vars].sort();
    if (vs.length > 6) throw new Error(`${vs.length} variables; the truth table is limited to 6`);
    return { exprs, vars: vs };
}
function emitExpr(c, e, env) {
    switch (e.op) {
        case 'const': return e.v;
        case 'var': return env[e.name];
        case 'not': return NOT(c, emitExpr(c, e.a, env));
        case 'and': return AND(c, emitExpr(c, e.a, env), emitExpr(c, e.b, env));
        case 'or': return OR(c, emitExpr(c, e.a, env), emitExpr(c, e.b, env));
        case 'xor': return XOR(c, emitExpr(c, e.a, env), emitExpr(c, e.b, env));
    }
}
function evalExpr(e, env) {
    switch (e.op) {
        case 'const': return e.v;
        case 'var': return env[e.name];
        case 'not': return 1 - evalExpr(e.a, env);
        case 'and': return evalExpr(e.a, env) & evalExpr(e.b, env);
        case 'or': return evalExpr(e.a, env) | evalExpr(e.b, env);
        case 'xor': return evalExpr(e.a, env) ^ evalExpr(e.b, env);
    }
}

function makeExprTask(src) {
    const { exprs, vars } = parseExprs(src), nv = vars.length, lanes = 2 ** nv, c = newCircuit(), outs = [];
    const laneEnv = k => Object.fromEntries(vars.map((v, i) => [v, (k >> (nv - 1 - i)) & 1]));
    for (let k = 0; k < lanes; k++) {
        const env = Object.fromEntries(vars.map(v => [v, input(c, `${v} (row ${k})`)]));
        exprs.forEach(({ name, ast }) => { c.tag = `${name}, row ${k}`; outs.push(emitExpr(c, ast, env)); });
    }
    const t = {
        type: 'expr', fab: scheduleFabric(c, outs), title: `${exprs.length} expression(s) · ${nv} var(s) · ${lanes} parallel lanes`,
        begin() { t.o = null; t.ok = null; },
        cycleInputs() { const v = []; for (let k = 0; k < lanes; k++) { const env = laneEnv(k); for (const x of vars) v.push(env[x]); } return Uint8Array.from(v); },
        endCycle(o) { t.o = o; t.ok = true; for (let k = 0; k < lanes; k++) exprs.forEach(({ ast }, j) => { if (evalExpr(ast, laneEnv(k)) !== o[k * exprs.length + j]) t.ok = false; }); return false; },
        cycleLabel() { return 'truth table'; },
        report() {
            const w = s => s.padEnd(Math.max(1, s.length));
            const head = `${vars.map(w).join(' ')} │ ${exprs.map(e => e.name).join(' ')}`;
            const lines = [head, '─'.repeat(head.length)];
            for (let k = 0; k < lanes; k++) {
                const env = laneEnv(k);
                const res = t.o ? exprs.map((e, j) => String(t.o[k * exprs.length + j]).padEnd(e.name.length)).join(' ') : exprs.map(e => '·'.padEnd(e.name.length)).join(' ');
                lines.push(`${vars.map(v => String(env[v]).padEnd(v.length)).join(' ')} │ ${res}`);
            }
            return lines.join('\n');
        },
        refLine() { return t.ok === null ? '—' : t.ok ? `✓ all ${lanes} rows match JS evaluation` : '✗ differs from JS evaluation'; },
    };
    return t;
}

// ---------------------------------------------------------------- script compiler (JavaScript-style subset -> CPU assembly)
//
// Variables live in the CPU's 4 registers (declared names get fixed registers, the rest are
// expression temporaries). Values are 8-bit and wrap; comparisons are unsigned. Loops are
// emitted test-at-bottom so every condition only needs a "jump if true" form.

const SCRIPTS = {
    fib: `// 16-bit Fibonacci on the 8-bit CPU: each number is two bytes (hi, lo) and
// the add carries from the low byte into the high byte by hand.
// out: u16  (each pair of OUT bytes, high then low, is one 16-bit number)
let alo = 0, ahi = 0, blo = 1, bhi = 0, lo, hi;
while (true) {
    out(ahi); out(alo);
    lo = alo + blo;
    hi = ahi + bhi;
    if (lo < blo) hi++;                            // carry out of the low byte
    if (hi < bhi || (hi == bhi && lo < blo)) break; // passed 65535
    alo = blo; ahi = bhi;
    blo = lo; bhi = hi;
}
out(bhi); out(blo);`,
    mul: `// 13 x 11 by shift-and-add
let a = 13, b = 11, p = 0;
while (b != 0) {
    if (b & 1) p += a;
    a <<= 1;
    b >>= 1;
}
out(p);`,
    gcd: `// Euclid by repeated subtraction
let a = 84, b = 36;
while (b != 0) {
    if (a < b) { let t = a; a = b; b = t; }
    else a -= b;
}
out(a);`,
    primes: `// primes below 40 by trial division
for (let n = 2; n < 40; n++) {
    let d = 2;
    while (d < n) {
        let r = n;
        while (r >= d) r -= d;   // r = n % d
        if (r == 0) break;
        d++;
    }
    if (d == n) out(n);
}`,
    countdown: `// count down from 10
let i = 10;
while (i != 0) {
    out(i);
    i--;
}
out(i);`,
    collatz: `// Collatz sequence from 7, then the number of steps
let x = 7, steps = 0;
while (x != 1) {
    out(x);
    if (x & 1) x = x + x + x + 1;
    else x >>= 1;
    steps++;
}
out(steps);`,
    bubble: `// bubble sort of 4 random numbers. The CPU has no RAM, so the "list" is
// the 4 variables (= the 4 registers); ^= swaps need no spare register.
let a = $RAND, b = $RAND, c = $RAND, d = $RAND;
out(a); out(b); out(c); out(d);
while (b < a || c < b || d < c) {
    if (b < a) { a ^= b; b ^= a; a ^= b; }
    if (c < b) { b ^= c; c ^= b; b ^= c; }
    if (d < c) { c ^= d; d ^= c; c ^= d; }
}
out(a); out(b); out(c); out(d);`,
    sincos: `// sine and cosine by Minsky's circle algorithm (HAKMEM item 149):
// only shifts and adds. Values are stored as 128 + v (128 is zero), so
// t >>= 1; t += 64 is a signed shift. Two turns of radius 60.
// plot: sin, cos
let c = 188, s = 128, t, n = 100;
while (n != 0) {
    out(s); out(c);
    t = s; t >>= 1; t += 64; t >>= 1; t += 64; t >>= 1; t += 64;
    c -= t; c += 128;           // cos -= sin / 8
    t = c; t >>= 1; t += 64; t >>= 1; t += 64; t >>= 1; t += 64;
    s += t; s += 128;           // sin += cos / 8
    n--;
}`,
    lcg: `// pseudo-random numbers: x = 5x + 17 (mod 256), a full-period
// linear congruential generator (5x = (x << 2) + x)
let x = $RAND, t, n = 40;
while (n != 0) {
    t = x << 2;
    x += t;
    x += 17;
    out(x);
    n--;
}`,
    divmod: `// 200 / 7 by repeated subtraction: prints quotient, then remainder
let n = 200, d = 7, q = 0;
while (n >= d) { n -= d; q++; }
out(q); out(n);`,
    isqrt: `// integer square root of 200 by subtracting odd numbers:
// 1 + 3 + 5 + ... + (2r - 1) = r * r
let x = 200, odd = 1, r = 0;
while (x >= odd) { x -= odd; odd += 2; r++; }
out(r);`,
    popcount: `// count the 1 bits in 0b10110111
let x = 0b10110111, n = 0, t;
while (x != 0) { t = x & 1; n += t; x >>= 1; }
out(n);`,
    sort8: `// bubble sort of 8 random numbers stored in RAM
let a = [$RAND, $RAND, $RAND, $RAND, $RAND, $RAND, $RAND, $RAND];
let n = 8, i, x, y;
for (i = 0; i < n; i++) out(a[i]);          // the list as loaded
while (n != 1) {                            // each pass bubbles the largest up
    n--;
    for (i = 0; i < n; i++) {
        x = a[i]; y = a[i + 1];
        if (y < x) { a[i] = y; a[i + 1] = x; }
    }
}
for (i = 0; i < 8; i++) out(a[i]);          // sorted`,
    sieve: `// sieve of Eratosthenes: primes below 16, one flag byte per number
let composite[16];
for (let p = 2; p < 16; p++) {
    if (composite[p]) continue;
    out(p);
    for (let m = p + p; m < 16; m += p) composite[m] = 1;
}`,
    reverse: `// reverse an array in place, swapping from both ends
let a = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
let i = 0, j = 9, t;
while (i < j) { t = a[i]; a[i] = a[j]; a[j] = t; i++; j--; }
for (i = 0; i < 10; i++) out(a[i]);`,
    running: `// running totals: each element becomes the sum of itself and all before it
let a = [3, 1, 4, 1, 5, 9, 2, 6];
for (let i = 1; i < 8; i++) a[i] += a[i - 1];
for (let i = 0; i < 8; i++) out(a[i]);
// plot: running total`,
    stack: `// a stack in RAM: push 5 numbers, then pop them (last in, first out)
let stack[8], sp = 0, v = 10;
while (sp < 5) { stack[sp] = v; sp++; v += 7; }
while (sp != 0) { sp--; out(stack[sp]); }`,
    manyvars: `// more than 4 variables: the least-used ones live in RAM automatically
let a = 1, b = 1, c, d, e, f, g, h;
c = a + b; d = b + c; e = c + d; f = d + e; g = e + f; h = f + g;
out(a); out(b); out(c); out(d); out(e); out(f); out(g); out(h);`,
};

const SCRIPT_KEYWORDS = new Set(['let', 'var', 'const', 'if', 'else', 'while', 'for', 'break', 'continue', 'out', 'print', 'halt', 'true', 'false']);
const SCRIPT_OPS = { '+': 'ADD', '-': 'SUB', '&': 'AND', '|': 'OR', '^': 'XOR' };
const SCRIPT_NEG = { '<': '>=', '>=': '<', '>': '<=', '<=': '>', '==': '!=', '!=': '==' };

function lexScript(src) {
    const toks = [], re = /(\s+)|(\/\/[^\n]*)|(\/\*[\s\S]*?\*\/)|(0x[0-9a-fA-F]+|0b[01]+|\d+)|([A-Za-z_]\w*)|(<<=|>>=|\+\+|--|\+=|-=|&=|\|=|\^=|<<|>>|<=|>=|==|!=|&&|\|\||[-+*/%&|^~!<>=(){};,\[\]])/y;
    let line = 1, i = 0;
    while (i < src.length) {
        re.lastIndex = i;
        const m = re.exec(src);
        if (!m) throw new Error(`line ${line}: unexpected character '${src[i]}'`);
        if (m[4]) toks.push({ t: 'num', v: Number(m[0]), line });
        else if (m[5]) toks.push({ t: SCRIPT_KEYWORDS.has(m[0]) ? 'kw' : 'id', v: m[0], line });
        else if (m[6]) toks.push({ t: 'op', v: m[0], line });
        line += (m[0].match(/\n/g) || []).length;
        i = re.lastIndex;
    }
    toks.push({ t: 'eof', v: 'end of script', line });
    return toks;
}

const sBin = (op, a, b, line) => ({ k: 'bin', op, a, b, line });
const sNum = v => ({ k: 'num', v });
function foldScript(e) {
    if (e.k === 'un' && e.a.k === 'num') { const v = e.a.v; return sNum(e.op === '-' ? (-v) & 255 : e.op === '~' ? (~v) & 255 : +!v); }
    if (e.k !== 'bin' || e.a.k !== 'num' || e.b.k !== 'num') return e;
    const x = e.a.v, y = e.b.v;
    const f = { '+': x + y, '-': x - y, '*': x * y, '&': x & y, '|': x | y, '^': x ^ y, '<<': y > 7 ? 0 : x << y, '>>': y > 7 ? 0 : x >> y, '<': x < y, '>': x > y, '<=': x <= y, '>=': x >= y, '==': x === y, '!=': x !== y, '&&': !!(x && y), '||': !!(x || y), '/': y ? Math.floor(x / y) : 0, '%': y ? x % y : 0 }[e.op];
    return sNum(Number(f) & 255);
}

function parseScript(src) {
    const toks = lexScript(src);
    let p = 0;
    const peek = () => toks[p], next = () => toks[p++];
    const fail = (msg, tk = peek()) => { throw new Error(`line ${tk.line}: ${msg}`); };
    const is = v => peek().t !== 'num' && peek().v === v;
    const eat = v => { if (!is(v)) fail(`expected '${v}' but found '${peek().v}'`); return next(); };
    const ident = () => { const tk = next(); if (tk.t !== 'id') fail(`expected a variable name, found '${tk.v}'`, tk); return tk.v; };
    const LEVELS = [['||'], ['&&'], ['|'], ['^'], ['&'], ['==', '!='], ['<', '>', '<=', '>='], ['<<', '>>'], ['+', '-'], ['*', '/', '%']];
    function expr(lvl = 0) {
        if (lvl === LEVELS.length) return unary();
        let a = expr(lvl + 1);
        while (peek().t === 'op' && LEVELS[lvl].includes(peek().v)) { const tk = next(); a = foldScript(sBin(tk.v, a, expr(lvl + 1), tk.line)); }
        return a;
    }
    function unary() {
        const tk = peek();
        if (tk.t === 'op' && (tk.v === '-' || tk.v === '~' || tk.v === '!')) { next(); return foldScript({ k: 'un', op: tk.v, a: unary(), line: tk.line }); }
        if (tk.t === 'op' && tk.v === '+') { next(); return unary(); }
        return primary();
    }
    const index = () => { eat('['); const e = expr(); eat(']'); return e; };
    function primary() {
        const tk = next();
        if (tk.t === 'num') { if (tk.v > 255) fail(`${tk.v} doesn't fit in 8 bits (0-255)`, tk); return sNum(tk.v); }
        if (tk.v === 'true' || tk.v === 'false') return sNum(+(tk.v === 'true'));
        if (tk.t === 'id') return is('[') ? { k: 'idx', name: tk.v, index: index(), line: tk.line } : { k: 'var', name: tk.v, line: tk.line };
        if (tk.t === 'op' && tk.v === '(') { const e = expr(); eat(')'); return e; }
        fail(`unexpected '${tk.v}'`, tk);
    }
    // an assignment target: a scalar or an array element; produces an assign or a store statement
    function target(name, line) {
        if (!is('[')) { const v = { k: 'var', name, line }; return { read: v, set: e => ({ k: 'assign', name, e, line }) }; }
        const i = index(), v = { k: 'idx', name, index: i, line };
        return { read: v, set: e => ({ k: 'store', name, index: i, e, line }) };
    }
    function simple() {
        const tk = peek();
        if (is('++') || is('--')) { next(); const t = target(ident(), tk.line); return t.set(sBin(tk.v[0], t.read, sNum(1), tk.line)); }
        const t = target(ident(), tk.line), op = next();
        if (op.v === '++' || op.v === '--') return t.set(sBin(op.v[0], t.read, sNum(1), tk.line));
        if (op.v === '=') return t.set(expr());
        if (op.t === 'op' && /^(\+|-|&|\||\^|<<|>>)=$/.test(op.v)) return t.set(foldScript(sBin(op.v.slice(0, -1), t.read, expr(), tk.line)));
        fail(`expected '=' after '${t.read.name}'`, op);
    }
    function decl() {
        const kw = next(), items = [];
        do {
            const tk = peek(), name = ident();
            if (is('[')) {
                next(); const n = next();
                if (n.t !== 'num' || n.v < 1 || n.v > 16) fail('array size must be a number from 1 to 16', n);
                eat(']'); items.push({ name, array: true, size: n.v, init: null, line: tk.line });
            } else if (is('=')) {
                next();
                if (is('[')) {
                    next(); const vals = [];
                    while (!is(']')) {
                        const e = expr();
                        if (e.k !== 'num') fail('array initial values must be constants');
                        vals.push(e.v);
                        if (!is(']')) eat(',');
                    }
                    next();
                    if (!vals.length || vals.length > 16) fail('an array literal needs 1 to 16 values', tk);
                    items.push({ name, array: true, size: vals.length, init: vals, line: tk.line });
                } else items.push({ name, e: expr(), line: tk.line });
            } else items.push({ name, e: null, line: tk.line });
        } while (is(',') && next());
        return { k: 'decl', items, line: kw.line };
    }
    const isDecl = () => is('let') || is('var') || is('const');
    function stmt() {
        const tk = peek();
        if (is('{')) { next(); const body = []; while (!is('}')) { if (peek().t === 'eof') fail("missing '}'"); body.push(stmt()); } next(); return { k: 'block', body }; }
        if (is(';')) { next(); return { k: 'block', body: [] }; }
        if (isDecl()) { const d = decl(); eat(';'); return d; }
        if (is('if')) { next(); eat('('); const c = expr(); eat(')'); const s = stmt(); let e = null; if (is('else')) { next(); e = stmt(); } return { k: 'if', c, s, e, line: tk.line }; }
        if (is('while')) { next(); eat('('); const c = expr(); eat(')'); return { k: 'while', c, s: stmt(), line: tk.line }; }
        if (is('for')) {
            next(); eat('(');
            const init = is(';') ? null : isDecl() ? decl() : simple(); eat(';');
            const c = is(';') ? sNum(1) : expr(); eat(';');
            const step = is(')') ? null : simple(); eat(')');
            return { k: 'for', init, c, step, s: stmt(), line: tk.line };
        }
        if (is('break') || is('continue')) { next(); eat(';'); return { k: tk.v, line: tk.line }; }
        if (is('out') || is('print')) { next(); eat('('); const e = expr(); eat(')'); eat(';'); return { k: 'out', e, line: tk.line }; }
        if (is('halt')) { next(); eat('('); eat(')'); eat(';'); return { k: 'halt', line: tk.line }; }
        const s = simple(); eat(';'); return s;
    }
    const body = [];
    while (peek().t !== 'eof') body.push(stmt());
    return { k: 'block', body };
}

const scriptReads = (e, name) => e.k === 'var' ? e.name === name : e.k === 'num' ? false : e.k === 'idx' ? scriptReads(e.index, name) : e.k === 'un' ? scriptReads(e.a, name) : scriptReads(e.a, name) || scriptReads(e.b, name);
function negateScript(e) {
    if (e.k === 'num') return sNum(+!e.v);
    if (e.k === 'un' && e.op === '!') return e.a;
    if (e.k === 'bin' && SCRIPT_NEG[e.op]) return { ...e, op: SCRIPT_NEG[e.op] };
    if (e.k === 'bin' && (e.op === '&&' || e.op === '||')) return { ...e, op: e.op === '&&' ? '||' : '&&', a: negateScript(e.a), b: negateScript(e.b) };
    return sBin('==', e, sNum(0), e.line);
}

// Storage: arrays are laid out in RAM from address 0 in declaration order. Scalar variables go in
// registers, most-used first (uses inside loops weigh 8x per level); registers not given to
// variables are expression temporaries. When there are more variables than fit (or the code needs
// more temporaries), the least-used scalars live in RAM after the arrays. Every register/RAM split
// that fits is compiled and the shortest program wins.
function compileScript(src) {
    const ast = parseScript(src), srcLines = src.split('\n');
    const scalars = [], arrays = new Map(), uses = new Map();
    const bump = (name, w) => uses.set(name, (uses.get(name) || 0) + w);
    function countE(e, w) { if (!e) return; if (e.k === 'var') bump(e.name, w); else if (e.k === 'idx') countE(e.index, w); else if (e.k === 'un') countE(e.a, w); else if (e.k === 'bin') { countE(e.a, w); countE(e.b, w); } }
    (function walk(s, w) {
        if (!s) return;
        switch (s.k) {
            case 'block': s.body.forEach(x => walk(x, w)); break;
            case 'decl': s.items.forEach(it => {
                const clash = it.array ? scalars.includes(it.name) : arrays.has(it.name);
                if (clash) throw new Error(`line ${it.line}: '${it.name}' is declared as both an array and a variable`);
                if (it.array) { if (arrays.has(it.name)) throw new Error(`line ${it.line}: array '${it.name}' is declared twice`); arrays.set(it.name, { size: it.size, init: it.init }); }
                else { if (!scalars.includes(it.name)) scalars.push(it.name); if (it.e) { bump(it.name, w); countE(it.e, w); } }
            }); break;
            case 'assign': bump(s.name, w); countE(s.e, w); break;
            case 'store': countE(s.index, w); countE(s.e, w); break;
            case 'out': countE(s.e, w); break;
            case 'if': countE(s.c, w); walk(s.s, w); walk(s.e, w); break;
            case 'while': countE(s.c, w * 8); walk(s.s, w * 8); break;
            case 'for': walk(s.init, w); countE(s.c, w * 8); walk(s.step, w * 8); walk(s.s, w * 8); break;
        }
    })(ast, 1);
    let arrBytes = 0;
    for (const a of arrays.values()) { a.base = arrBytes; arrBytes += a.size; }
    if (arrBytes > RAM_BYTES) throw new Error(`arrays need ${arrBytes} bytes but the RAM has ${RAM_BYTES}`);
    const ram = new Uint8Array(RAM_BYTES);
    for (const a of arrays.values()) if (a.init) a.init.forEach((v, i) => ram[a.base + i] = v & 255);
    const ranked = [...scalars].sort((x, y) => (uses.get(y) || 0) - (uses.get(x) || 0));
    let best = null, firstErr = null;
    for (let k = Math.min(4, ranked.length); k >= 0; k--) {
        const inRam = ranked.slice(k);
        if (arrBytes + inRam.length > RAM_BYTES) { firstErr = firstErr || new Error(`not enough storage: ${scalars.length} variables and ${arrBytes} bytes of arrays exceed 4 registers + ${RAM_BYTES} bytes of RAM`); break; }
        try {
            const r = genScript(ast, srcLines, ranked.slice(0, k), inRam, arrays, arrBytes, ram);
            if (!best || r.size < best.size) best = r;
        } catch (err) { if (!/too complex/.test(err.message)) throw err; firstErr = firstErr || err; }
    }
    if (!best) throw firstErr;
    return best;
}

function genScript(ast, srcLines, regVars, memVars, arrays, arrBytes, ram) {
    const regOf = new Map(regVars.map((n, i) => [n, i])), memOf = new Map(memVars.map((n, i) => [n, arrBytes + i]));
    const out = [], loops = [], temps = [0, 1, 2, 3].slice(regVars.length);
    let inUse = 0, labelN = 0, lastLine = 0;
    const R = r => `r${r}`, emit = ins => out.push({ ins }), label = () => `L${labelN++}`, place = l => out.push({ label: l });
    const temp = line => {
        if (inUse >= temps.length) throw new Error(`line ${line}: expression too complex - ${regVars.length} variable(s) in registers leave ${temps.length} of the 4 for temporaries; split it into simpler statements`);
        return temps[inUse++];
    };
    const known = (name, line) => {
        if (regOf.has(name) || memOf.has(name)) return;
        if (arrays.has(name)) throw new Error(`line ${line}: '${name}' is an array - use ${name}[index]`);
        throw new Error(`line ${line}: '${name}' is not declared (use let ${name} = ...)`);
    };
    const isRegVar = e => e.k === 'var' && regOf.has(e.name);
    const reg = name => regOf.get(name);
    const operand = e => { if (isRegVar(e)) return reg(e.name); const r = temp(e.line); gen(e, r); return r; };
    // LD or ST between register r and array element e: constant index -> absolute address,
    // otherwise [index + base], folding a constant +/- k in the index into the 4-bit offset
    function memAccess(op, r, e) {
        const arr = arrays.get(e.name);
        if (!arr) { if (regOf.has(e.name) || memOf.has(e.name)) throw new Error(`line ${e.line}: '${e.name}' is not an array`); known(e.name, e.line); }
        let idx = e.index, off = arr.base;
        if (idx.k === 'num') return emit(`${op} ${R(r)}, [${(arr.base + idx.v) & 15}]`);
        if (idx.k === 'bin' && (idx.op === '+' || idx.op === '-') && idx.b.k === 'num') {
            const o = arr.base + (idx.op === '+' ? idx.b.v : -idx.b.v);
            if (o >= 0 && o <= 15) { off = o; idx = idx.a; }
        } else if (idx.k === 'bin' && idx.op === '+' && idx.a.k === 'num' && arr.base + idx.a.v <= 15) { off = arr.base + idx.a.v; idx = idx.b; }
        const m = inUse, ri = operand(idx);
        emit(`${op} ${R(r)}, [${R(ri)}${off ? '+' + off : ''}]`);
        inUse = m;
    }

    // gen(e, t): evaluate e into register t (callers guarantee e never reads the variable held in t)
    function gen(e, t) {
        const line = e.line;
        if (e.k === 'num') return emit(`LDI ${R(t)}, ${e.v}`);
        if (e.k === 'var') {
            known(e.name, line);
            if (memOf.has(e.name)) return emit(`LD ${R(t)}, [${memOf.get(e.name)}]`);
            const r = reg(e.name); if (r !== t) emit(`MOV ${R(t)}, ${R(r)}`); return;
        }
        if (e.k === 'idx') return memAccess('LD', t, e);
        if (e.k === 'un') {
            if (e.op === '!') return genBool(e, t);
            const m = inUse, src = operand(e.a);
            emit(`LDI ${R(t)}, ${e.op === '-' ? 0 : 255}`); emit(`${e.op === '-' ? 'SUB' : 'XOR'} ${R(t)}, ${R(src)}`);
            inUse = m; return;
        }
        if (SCRIPT_NEG[e.op] || e.op === '&&' || e.op === '||') return genBool(e, t);
        let { a, b } = e;
        const op = e.op;
        if (a.k === 'num' && ['+', '&', '|', '^'].includes(op)) [a, b] = [b, a];
        if (b.k === 'num' && ['&', '|', '^'].includes(op) && isRegVar(a)) { emit(`LDI ${R(t)}, ${b.v}`); emit(`${SCRIPT_OPS[op]} ${R(t)}, ${R(reg(a.name))}`); return; }
        if (a.k === 'num' && op === '-') { emit(`LDI ${R(t)}, ${a.v}`); return applyOp(op, b, t, line); }
        gen(a, t); applyOp(op, b, t, line);
    }
    // t already holds the left operand
    function applyOp(op, b, t, line) {
        if (op === '<<' || op === '>>' || op === '*') {
            if (b.k !== 'num') throw new Error(`line ${line}: ${op === '*' ? 'multiply needs a constant power of two - there is no multiply instruction (use a loop)' : 'shift amount must be a constant'}`);
            let k = b.v;
            if (op === '*') { if (k === 0) return emit(`LDI ${R(t)}, 0`); if (k & (k - 1)) throw new Error(`line ${line}: can only multiply by a power of two - there is no multiply instruction (use a loop)`); k = Math.log2(k); }
            if (k > 7) return emit(`LDI ${R(t)}, 0`);
            for (let i = 0; i < k; i++) emit(`${op === '>>' ? 'SHR' : 'SHL'} ${R(t)}`);
            return;
        }
        if (op === '/' || op === '%') throw new Error(`line ${line}: '${op}' is not supported - there is no divide instruction (use a loop)`);
        if (b.k === 'num' && (op === '+' || op === '-')) { const c = op === '+' ? b.v : (-b.v) & 255; if (c) emit(`ADDI ${R(t)}, ${c}`); return; }
        const m = inUse, src = operand(b);
        emit(`${SCRIPT_OPS[op]} ${R(t)}, ${R(src)}`);
        inUse = m;
    }
    function genBool(e, t) { const L = label(); emit(`LDI ${R(t)}, 1`); jumpTrue(e, L); emit(`LDI ${R(t)}, 0`); place(L); }
    function jumpTrue(e, L) {
        if (e.k === 'num') { if (e.v) emit(`JMP ${L}`); return; }
        if (e.k === 'un' && e.op === '!') return jumpTrue(negateScript(e.a), L);
        if (e.k === 'bin' && e.op === '||') { jumpTrue(e.a, L); jumpTrue(e.b, L); return; }
        if (e.k === 'bin' && e.op === '&&') { const skip = label(); jumpTrue(negateScript(e.a), skip); jumpTrue(e.b, L); place(skip); return; }
        const m = inUse;
        if (e.k === 'bin' && (e.op === '==' || e.op === '!=')) {
            let { a, b } = e;
            if (a.k === 'num' && a.v === 0) [a, b] = [b, a];
            let r;
            if (b.k === 'num' && b.v === 0) r = operand(a); else { r = temp(e.line); gen(sBin('^', a, b, e.line), r); }
            emit(`${e.op === '==' ? 'JZ' : 'JNZ'} ${R(r)}, ${L}`);
        } else if (e.k === 'bin' && SCRIPT_NEG[e.op]) {
            const ra = operand(e.a), rb = operand(e.b);
            if (e.op === '<') emit(`JLT ${R(ra)}, ${R(rb)}, ${L}`);
            else if (e.op === '>') emit(`JLT ${R(rb)}, ${R(ra)}, ${L}`);
            else { const skip = label(); emit(e.op === '>=' ? `JLT ${R(ra)}, ${R(rb)}, ${skip}` : `JLT ${R(rb)}, ${R(ra)}, ${skip}`); emit(`JMP ${L}`); place(skip); }
        } else emit(`JNZ ${R(operand(e))}, ${L}`);
        inUse = m;
    }
    function assign(name, e, line) {
        known(name, line);
        if (e.k === 'var' && e.name === name) return;
        if (memOf.has(name)) {
            const addr = memOf.get(name);
            if (isRegVar(e)) return emit(`ST ${R(reg(e.name))}, [${addr}]`);
            const m = inUse, t = temp(line); gen(e, t); emit(`ST ${R(t)}, [${addr}]`); inUse = m; return;
        }
        const r = reg(name);
        if (!scriptReads(e, name)) return gen(e, r);
        if (e.k === 'bin' && (SCRIPT_OPS[e.op] || ['<<', '>>', '*'].includes(e.op))) {
            let { a, b } = e;
            const isT = x => x.k === 'var' && x.name === name;
            if (!isT(a) && isT(b) && ['+', '&', '|', '^'].includes(e.op)) [a, b] = [b, a];
            if (isT(a) && !scriptReads(b, name)) return applyOp(e.op, b, r, line);
        }
        const m = inUse, t = temp(line);
        gen(e, t); emit(`MOV ${R(r)}, ${R(t)}`);
        inUse = m;
    }
    function store(s) {
        const m = inUse, v = isRegVar(s.e) ? reg(s.e.name) : (() => { const t = temp(s.line); gen(s.e, t); return t; })();
        memAccess('ST', v, { k: 'idx', name: s.name, index: s.index, line: s.line });
        inUse = m;
    }
    const note = line => { if (line && line !== lastLine) { lastLine = line; out.push({ comment: `${line}: ${srcLines[line - 1].trim()}` }); } };
    const loneJump = s => s.k === 'break' || s.k === 'continue' ? s : s.k === 'block' && s.body.length === 1 && (s.body[0].k === 'break' || s.body[0].k === 'continue') ? s.body[0] : null;
    function stmt(s) {
        note(s.line);
        switch (s.k) {
            case 'block': s.body.forEach(stmt); break;
            case 'decl': s.items.forEach(it => { if (!it.array && it.e) assign(it.name, it.e, it.line); }); break;
            case 'assign': assign(s.name, s.e, s.line); break;
            case 'store': store(s); break;
            case 'out': { const m = inUse; emit(`OUT ${R(operand(s.e))}`); inUse = m; break; }
            case 'halt': emit('HALT'); break;
            case 'break': case 'continue': {
                const lp = loops[loops.length - 1];
                if (!lp) throw new Error(`line ${s.line}: '${s.k}' outside a loop`);
                emit(`JMP ${s.k === 'break' ? lp.end : lp.cont}`); break;
            }
            case 'if': {
                const lone = loneJump(s.s);
                if (lone && !s.e && loops.length) { const lp = loops[loops.length - 1]; jumpTrue(s.c, lone.k === 'break' ? lp.end : lp.cont); break; }
                const elseL = label();
                jumpTrue(negateScript(s.c), elseL); stmt(s.s);
                if (s.e) { const end = label(); emit(`JMP ${end}`); place(elseL); stmt(s.e); place(end); } else place(elseL);
                break;
            }
            case 'while': case 'for': {
                if (s.k === 'for' && s.init) stmt(s.init);
                if (s.c.k === 'num' && !s.c.v) break;
                const forever = s.c.k === 'num', top = label(), cont = label(), test = label(), end = label();
                if (!forever) emit(`JMP ${test}`);
                place(top); loops.push({ end, cont }); stmt(s.s); loops.pop();
                place(cont); if (s.k === 'for' && s.step) stmt(s.step);
                place(test); if (forever) emit(`JMP ${top}`); else jumpTrue(s.c, top);
                place(end); break;
            }
        }
    }
    stmt(ast);
    const lastIns = [...out].reverse().find(x => x.ins);
    if (!lastIns || lastIns.ins !== 'HALT') emit('HALT');
    // peephole: drop "JMP L" when L labels the next instruction
    for (let changed = true; changed;) {
        changed = false;
        for (let i = 0; i < out.length; i++) {
            const m = /^JMP (L\d+)$/.exec(out[i].ins || '');
            if (!m) continue;
            let hit = false;
            for (let j = i + 1; j < out.length && !out[j].ins; j++) if (out[j].label === m[1]) hit = true;
            if (hit) { out.splice(i, 1); changed = true; }
        }
    }
    const used = new Set(out.filter(x => x.ins).map(x => (x.ins.match(/L\d+$/) || [])[0]).filter(Boolean));
    const parts = [`registers: ${[...regOf].map(([n, r]) => `${n}=r${r}`).join(', ') || 'none'}`];
    if (memOf.size) parts.push(`in RAM: ${[...memOf].map(([n, a]) => `${n}=[${a}]`).join(', ')}`);
    if (arrays.size) parts.push(`arrays: ${[...arrays].map(([n, a]) => `${n}=[${a.base}..${a.base + a.size - 1}]`).join(', ')}`);
    const lines = [`; compiled from script - ${parts.join('; ')}`];
    let last = -1; ram.forEach((v, i) => { if (v) last = i; });
    if (last >= 0) lines.push(`      .data ${Array.from(ram.slice(0, last + 1)).join(', ')}`);
    for (const x of out) {
        if (x.comment) lines.push(`; ${x.comment}`);
        else if (x.label) { if (used.has(x.label)) lines.push(`${x.label}:`); }
        else lines.push(`      ${x.ins}`);
    }
    return { asm: lines.join('\n'), regOf, memOf, arrays, size: out.filter(x => x.ins).length };
}

function makeScriptTask(src, maxCycles) {
    const { asm, regOf, memOf, arrays, size } = compileScript(src);
    let t;
    try { t = makeCpuTask(asm, maxCycles); } catch (err) { err.asm = asm; throw err; }
    const base = t.report;
    t.asm = asm;
    t.title = `Script → CPU · ${size}/${ROM_WORDS} instructions · ${regOf.size} reg var(s)${memOf.size ? ` · ${memOf.size} in RAM` : ''}${arrays.size ? ` · ${arrays.size} array(s)` : ''}`;
    t.report = st => {
        const vals = [...regOf].map(([n, r]) => `${n}=${t.s.R[r]}`).concat([...memOf].map(([n, a]) => `${n}=${t.s.ram[a]}`));
        const arrs = [...arrays].map(([n, a]) => `${n} = [${t.s.ram.slice(a.base, a.base + a.size).join(', ')}]`);
        return [`vars  ${vals.join('  ') || '(none)'}`, ...arrs, base(st)].join('\n');
    };
    return t;
}

// ---------------------------------------------------------------- classic free run (pure Rule 110, no host)
//
// The textbook spacetime diagram: one row, evolved generation after generation by Rule 110 alone.
// "Gliders" style classifies every cell by its 7x3 neighbourhood: windows that occur in the periodic
// ether (Cook's 14-cell background 11111000100110) are dimmed, everything else - gliders and
// their collisions - is coloured.

const ETHER = '11111000100110';
const CLS_UNKNOWN = 0, CLS_EMPTY = 1, CLS_ETHER = 2, CLS_STRUCT = 3;
const CLASSIC_PAL = { image: ['#f2f2f2', '#000000'], ether: ['#f2f2f2', '#b9b9b9'], struct: ['#ffe4e6', '#e11d48'] };
const CLASSIC_STARTS = {
    right: 'single live cell at the right edge', center: 'single live cell in the centre',
    random: 'random row', ether: 'ether background (11111000100110 repeated)', custom: 'custom pattern at the right edge',
};
let etherWindows = null;
function etherTable() {
    if (etherWindows) return etherWindows;
    const n = 14, T = 60;
    let row = Uint8Array.from(ETHER, ch => +ch);
    const rows = [row];
    for (let t = 1; t < T; t++) { const nx = new Uint8Array(n); for (let i = 0; i < n; i++) nx[i] = RULE_TABLE[(row[(i + n - 1) % n] << 2) | (row[i] << 1) | row[(i + 1) % n]]; rows.push(row = nx); }
    etherWindows = new Uint8Array(1 << 21);
    for (let t = 1; t < T - 1; t++) for (let i = 0; i < n; i++) {
        let m = 0;
        for (let dy = -1; dy <= 1; dy++) for (let dx = -3; dx <= 3; dx++) m = (m << 1) | rows[t + dy][(i + dx + n) % n];
        etherWindows[m] = 1;
    }
    return etherWindows;
}

function makeClassicTask({ width: W, gens, start, pattern, density, wrap }) {
    if (!(Number.isInteger(W) && W >= 8 && W <= 4000)) throw new Error('width must be 8-4000 cells');
    if (!(Number.isInteger(gens) && gens >= 1 && gens <= 20000)) throw new Error('generations must be 1-20000');
    const G = gens + 1;
    if (W * G > 8e6) throw new Error(`${W} × ${G} = ${(W * G / 1e6).toFixed(1)}M cells is too many (limit 8M) - reduce the width or generations`);
    const row0 = new Uint8Array(W);
    if (start === 'right') row0[W - 1] = 1;
    else if (start === 'center') row0[W >> 1] = 1;
    else if (start === 'random') for (let i = 0; i < W; i++) row0[i] = +(Math.random() < density);
    else if (start === 'ether') for (let i = 0; i < W; i++) row0[i] = +ETHER[i % 14];
    else {
        const bits = pattern.replace(/\s/g, '');
        if (!/^[01]+$/.test(bits)) throw new Error('custom pattern must contain only 0s and 1s');
        if (bits.length > W) throw new Error(`custom pattern is ${bits.length} cells, wider than the row (${W})`);
        for (let k = 0; k < bits.length; k++) row0[W - bits.length + k] = +bits[k];
    }
    const table = etherTable(), grid = new Uint8Array(W * G), cls = new Uint8Array(W * G);
    const fab = { classic: true, D: G, W, layers: [], outSrc: [], outIds: [], outIndex: new Map(), counts: [0, 0, 0, 0, 0, 0], nIn: 0 };
    const at = (r, i) => wrap ? grid[r * W + ((i % W) + W) % W] : i < 0 || i >= W ? 0 : grid[r * W + i];
    function classifyRow(r) {
        for (let i = 0; i < W; i++) {
            if (!wrap && (i < 3 || i > W - 4)) { cls[r * W + i] = CLS_UNKNOWN; continue; }
            let m = 0;
            for (let dy = -1; dy <= 1; dy++) for (let dx = -3; dx <= 3; dx++) m = (m << 1) | at(r + dy, i + dx);
            const c = m === 0 ? CLS_EMPTY : table[m] ? CLS_ETHER : CLS_STRUCT;
            cls[r * W + i] = c;
            if (c === CLS_ETHER) t.nEther++; else if (c === CLS_STRUCT) t.nStruct++;
        }
    }
    const t = {
        type: 'classic', fab, grid, cls, W, G, gens, wrap, start,
        title: `Classic free run · ${W} cells × ${gens} generations`,
        begin() { grid.fill(0); cls.fill(0); grid.set(row0); t.gen = 1; t.painted = 0; t.entry = null; t.nEther = 0; t.nStruct = 0; t.pop = row0.reduce((a, b) => a + b, 0); t.alive = t.pop; },
        advance() {
            const o = t.gen * W, p = o - W;
            let pop = 0;
            for (let i = 0; i < W; i++) {
                const l = i > 0 ? grid[p + i - 1] : wrap ? grid[p + W - 1] : 0, r = i + 1 < W ? grid[p + i + 1] : wrap ? grid[p] : 0;
                pop += grid[o + i] = RULE_TABLE[(l << 2) | (grid[p + i] << 1) | r];
            }
            t.pop = pop; t.alive += pop;
            if (t.gen >= 2) classifyRow(t.gen - 1);
            return ++t.gen < G;
        },
        cellClass: (r, i) => cls[r * W + i],
        report() {
            const inside = t.nEther + t.nStruct;
            return [
                `start   ${CLASSIC_STARTS[start]}`,
                `width ${W} · ${gens} generations · edges: ${wrap ? 'wrap around' : 'dead cells beyond'}`,
                '',
                `generation      ${t.gen - 1}/${gens}`,
                `population now  ${t.pop}`,
                `density so far  ${(100 * t.alive / (t.gen * W)).toFixed(1)}%`,
                `ether           ${inside ? (100 * t.nEther / inside).toFixed(1) + '%' : '—'} of the pattern`,
                `gliders etc.    ${inside ? (100 * t.nStruct / inside).toFixed(1) + '%' : '—'} (non-ether)`,
            ].join('\n');
        },
    };
    return t;
}

const isClassic = () => !!(state.fab && state.fab.classic);

function classicEntry() {
    const t = state.task, W = t.W;
    if (!t.entry) { const c = document.createElement('canvas'); c.width = W; c.height = t.G; const cx = c.getContext('2d'), img = cx.createImageData(W, t.G); t.entry = { canvas: c, ctx: cx, img, data: new Uint32Array(img.data.buffer) }; t.painted = 0; }
    const e = t.entry, from = Math.max(0, t.painted - 2), to = t.gen;
    if (to > from) {
        const style = state.classicStyle, inv = state.inverted ? 1 : 0, P = COL.classic;
        for (let r = from; r < to; r++) for (let i = 0; i < W; i++) {
            const k = r * W + i, v = t.grid[k] ^ inv, c = t.cls[k];
            e.data[k] = style === 'app' ? COL.raw[v] : style === 'gliders' && c === CLS_ETHER ? P.ether[v] : style === 'gliders' && c === CLS_STRUCT ? P.struct[v] : P.image[v];
        }
        e.ctx.putImageData(e.img, 0, 0, 0, from, W, to - from);
        t.painted = to;
    }
    return e;
}

function drawClassic() {
    const { sx, sy, rows, cols, x0, oy } = layout(), t = state.task, e = classicEntry();
    const visW = Math.min(cols, t.W - x0);
    ctx.fillStyle = state.classicStyle === 'app' ? '#0b1222' : CLASSIC_PAL.image[state.inverted ? 1 : 0];
    ctx.fillRect(0, oy, visW * sx, rows * sy);
    ctx.imageSmoothingEnabled = sx < 1;
    ctx.drawImage(e.canvas, x0, 0, visW, rows, 0, oy, visW * sx, rows * sy);
    const h = state.hover;
    if (h && h.classic) {
        const dpr = window.devicePixelRatio || 1;
        ctx.lineWidth = Math.max(1, dpr);
        ctx.strokeStyle = '#38bdf8';
        ctx.strokeRect((h.i - x0) * sx, oy + h.r * sy, Math.max(sx, 2), Math.max(sy, 2));
        if (h.r > 0) { ctx.strokeStyle = '#f59e0b'; ctx.strokeRect((h.i - 1 - x0) * sx, oy + (h.r - 1) * sy, Math.max(3 * sx, 2), Math.max(sy, 2)); }
    }
}

function classicHoverText() {
    const h = state.hover, t = state.task;
    if (!h || !h.classic) return null;
    const head = `generation ${h.r} · cell ${h.i}`;
    if (h.r >= t.gen) return `${head}\n(not computed yet)`;
    const v = t.grid[h.r * t.W + h.i], lines = [`${head} = ${v}`];
    if (h.r > 0) {
        const g = (i) => t.wrap ? t.grid[(h.r - 1) * t.W + ((i % t.W) + t.W) % t.W] : i < 0 || i >= t.W ? 0 : t.grid[(h.r - 1) * t.W + i];
        const l = g(h.i - 1), c = g(h.i), r = g(h.i + 1);
        lines.push(`parents  l c r = ${l} ${c} ${r}  → rule 110 case ${l}${c}${r} → ${RULE_TABLE[(l << 2) | (c << 1) | r]}`);
    } else lines.push('starting row');
    const c = t.cls[h.r * t.W + h.i];
    lines.push(`structure: ${c === CLS_ETHER ? 'ether (periodic background)' : c === CLS_STRUCT ? 'glider / collision (not ether)' : c === CLS_EMPTY ? 'empty (all-dead neighbourhood)' : h.r === 0 || h.r >= t.gen - 1 ? 'unclassified (needs the rows above and below)' : 'unclassified (edge)'}`);
    return lines.join('\n');
}

// ---------------------------------------------------------------- app state

const state = {
    task: null, fab: null,
    cycle: 0, layer: 0, done: false, playing: false, turbo: false,
    rows: [], scratch: [], hoverRows: [], hoverCycle: -1,
    inputs: null, cycleInputs: [],
    cells: 0, fabricOk: 0, fabricFail: -1,
    speed: 1,
    classicStyle: 'image',
    colorMode: 'roles', showLoad: true, inverted: false, highlightOut: true, readAt: 0, readCycle: -1,
    zoom: { cells: VIEW_CELLS, x0: 0, oy: 0 },
    front: { rows: [], cycle: -1, entry: null, painted: -1 }, liveStep: false,
    cache: new Map(), cacheCap: 32,
    hover: null, dirty: true, error: null,
};

// ---------------------------------------------------------------- run control

function setTask(task) {
    state.task = task; state.fab = task.fab;
    state.zoom = { cells: Math.min(VIEW_CELLS, task.fab.W), x0: 0, oy: 0 };
    if (task.fab.classic) state.zoom.cells = maxCells();
    state.rows = allocRows(task.fab); state.scratch = allocRows(task.fab); state.hoverRows = allocRows(task.fab); state.front.rows = allocRows(task.fab);
    const bytes = task.fab.W * task.fab.D * 2 * 4;
    state.cacheCap = Math.max(8, Math.min(256, Math.floor(160e6 / bytes)));
    resetRun();
}

function resetRun() {
    state.playing = state.turbo = false;
    state.cycle = 0; state.layer = 0; state.done = false;
    state.cycleInputs = []; state.cells = 0; state.fabricOk = 0; state.fabricFail = -1; state.hoverCycle = -1;
    state.cache.clear(); state.liveStep = false;
    Object.assign(state.front, { cycle: -1, entry: null, painted: -1 });
    if (state.task) state.task.begin();
    state.dirty = true;
}

function stepLayer() {
    const { fab, task } = state;
    if (!fab || state.done) return false;
    if (fab.classic) {
        const more = task.advance();
        state.cells += fab.W; state.layer = task.gen;
        if (!more) { state.done = true; state.cycle = 1; state.playing = state.turbo = false; }
        return true;
    }
    if (state.layer === 0) { state.inputs = task.cycleInputs(); state.cycleInputs[state.cycle] = state.inputs; }
    const L = state.layer, r = state.rows[L];
    runLayer(fab, L, L ? state.rows[L - 1].evo : null, state.inputs, r.load, r.evo);
    state.cells += r.evo.length;
    if (++state.layer === fab.D) finishCycle();
    return true;
}

function finishCycle() {
    const fab = state.fab, out = readOutputs(fab, state.rows[fab.D - 1].evo);
    const ref = evalCircuit(fab.circuit, state.inputs, fab.outIds);
    if (ref.every((v, i) => v === out[i])) state.fabricOk++; else if (state.fabricFail < 0) state.fabricFail = state.cycle;
    const e = state.cache.get(state.cycle);
    if (e) paintLayers(e, state.rows, e.painted, fab.D);
    state.rows.forEach((r, L) => { state.front.rows[L].load.set(r.load); state.front.rows[L].evo.set(r.evo); });
    state.front.cycle = state.cycle;
    const more = state.task.endCycle(out, state.cycle);
    state.cycle++; state.layer = 0;
    if (!more) { state.done = true; state.playing = state.turbo = false; }
}

function stepCycle() { if (state.done) return; do stepLayer(); while (state.layer !== 0 && !state.done); }

// ---------------------------------------------------------------- painting

function hexToAbgr(h) { const v = parseInt(h.slice(1), 16); return (0xff000000 | ((v & 0xff) << 16) | (v & 0xff00) | (v >> 16)) >>> 0; }
let COL = null;
function buildColors() {
    const p = pair => pair.map(hexToAbgr);
    COL = { classic: { image: p(CLASSIC_PAL.image), ether: p(CLASSIC_PAL.ether), struct: p(CLASSIC_PAL.struct) }, raw: p([PAL.dead, PAL.alive]), out: p(PAL.out), oper: p(PAL.oper), rail: p(PAL.rail), spill: p(PAL.spill), res: [] };
    for (const k of [K_NAND, K_OR, K_XOR, K_BUF]) COL.res[k] = p(PAL.res[k]);
}
const rowsPerLayer = () => isClassic() ? 1 : state.showLoad ? 2 : 1;

function paintRow(data, off, row, ly, evolved) {
    const raw = state.colorMode === 'raw', inv = state.inverted ? 1 : 0, hiOut = state.highlightOut;
    for (let j = 0; j < row.length; j++) {
        const v = row[j] ^ inv, slot = (j / 3) | 0, p = j - 3 * slot, k = ly.op[slot];
        let col;
        if (evolved && p === 1 && hiOut && ly.isOut[slot]) col = COL.out[v];
        else if (raw) col = COL.raw[v];
        else if (evolved) col = p === 1 ? COL.res[k][v] : COL.spill[v];
        else col = (k === K_NAND ? p === 1 : p === 0 || (k === K_BUF && p === 2)) ? COL.rail[v] : COL.oper[v];
        data[off + j] = col;
    }
}

function newEntry(k, cached = true) {
    const fab = state.fab, h = fab.D * rowsPerLayer(), canvas = document.createElement('canvas');
    canvas.width = fab.W; canvas.height = h;
    const ctx = canvas.getContext('2d'), img = ctx.createImageData(fab.W, h);
    const e = { canvas, ctx, img, data: new Uint32Array(img.data.buffer), painted: 0 };
    if (!cached) return e;
    state.cache.set(k, e);
    while (state.cache.size > state.cacheCap) state.cache.delete(state.cache.keys().next().value);
    return e;
}

function paintLayers(e, rows, from, to) {
    if (to <= from) return;
    const fab = state.fab, W = fab.W, rpl = rowsPerLayer();
    for (let L = from; L < to; L++) {
        const ly = fab.layers[L], r = rows[L];
        if (rpl === 2) paintRow(e.data, 2 * L * W, r.load, ly, false);
        paintRow(e.data, (L * rpl + rpl - 1) * W, r.evo, ly, true);
    }
    e.ctx.putImageData(e.img, 0, 0, 0, from * rpl, W, (to - from) * rpl);
    e.painted = to;
}

function getEntry(k, budget) {
    let e = state.cache.get(k);
    if (e) { state.cache.delete(k); state.cache.set(k, e); }
    if (k === state.cycle && !state.done) { if (!e) e = newEntry(k); paintLayers(e, state.rows, e.painted, state.layer); return e; }
    if (e && e.painted === state.fab.D) return e;
    if (budget.n <= 0) return null;
    budget.n--;
    if (!e) e = newEntry(k);
    simulateCycle(state.fab, state.cycleInputs[k], state.scratch);
    paintLayers(e, state.scratch, 0, state.fab.D);
    return e;
}

function invalidatePaint() { state.cache.clear(); state.front.entry = null; if (state.task && state.task.type === 'classic') state.task.entry = null; state.dirty = true; }

// Double buffer: while playing, only whole cycles are shown - each finished cycle is copied into
// state.front and swapped onto the canvas in one go. Manual layer stepping shows the live cycle.
function frontEntry() {
    const f = state.front;
    if (f.cycle < 0) return null;
    if (!f.entry) { f.entry = newEntry(f.cycle, false); f.painted = -1; }
    if (f.painted !== f.cycle) { paintLayers(f.entry, f.rows, 0, state.fab.D); f.painted = f.cycle; }
    return f.entry;
}

// ---------------------------------------------------------------- DOM

const $ = id => document.getElementById(id);
let canvas, ctx, container;

function resizeCanvas() {
    const dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(container.clientWidth * dpr); canvas.height = Math.round(container.clientHeight * dpr);
    if (state.fab) clampView();
    state.dirty = true;
}

const liveView = () => state.liveStep && !state.playing && state.layer > 0;
const shownCycle = () => liveView() || state.front.cycle < 0 ? state.cycle : state.front.cycle;

function layout() {
    const rows = state.fab.D * rowsPerLayer(), { cells: cols, x0, oy } = state.zoom, sx = canvas.width / cols;
    return { sx, sy: sx, rows, cols, x0, oy };
}

// Horizontal: x0 stays within the layer. Vertical: a block shorter than the canvas can be moved
// anywhere inside it; a taller one scrolls but never leaves a gap above or below.
function clampView() {
    const dpr = window.devicePixelRatio || 1, statusH = ($('status-bar').offsetHeight + 20) * dpr;
    const z = state.zoom, { sy, rows } = layout(), free = canvas.height - rows * sy - readStripH(sy) - statusH;
    z.x0 = Math.min(Math.max(0, state.fab.W - z.cells), Math.max(0, z.x0));
    z.oy = Math.min(Math.max(0, free), Math.max(Math.min(0, free), z.oy));
}

function panBy(dx, dy) {
    const z = state.zoom;
    z.x0 -= dx / layout().sx; z.oy += dy;
    clampView();
    state.dirty = true;
}

// zoom-out limit: the full layer width; a classic run may zoom out further, until the whole run fits
function maxCells() {
    const W = state.fab.W;
    if (!isClassic()) return W;
    const dpr = window.devicePixelRatio || 1, avail = Math.max(50, canvas.height - ($('status-bar').offsetHeight + 20) * dpr);
    return Math.max(W, Math.ceil(state.fab.D * canvas.width / avail));
}

function zoomAt(f, mx, my) {
    const W = state.fab.W, z = state.zoom, sx = canvas.width / z.cells, at = z.x0 + mx / sx;
    const cells = Math.min(maxCells(), Math.max(Math.min(MIN_VIEW_CELLS, W), z.cells * f)), nsx = canvas.width / cells;
    z.x0 = at - mx / nsx;
    z.oy = my - (my - z.oy) * nsx / sx;
    z.cells = cells;
    clampView();
    state.dirty = true;
}

function draw() {
    const cw = canvas.width, ch = canvas.height, dpr = window.devicePixelRatio || 1;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.fillStyle = PAL.bg; ctx.fillRect(0, 0, cw, ch);
    const fab = state.fab;
    if (!fab) return;
    if (fab.classic) return drawClassic();
    const { sx, sy, rows, cols, x0, oy } = layout(), e = liveView() ? getEntry(state.cycle, { n: 1 }) : frontEntry();
    ctx.fillStyle = '#0b1222'; ctx.fillRect(0, oy, cols * sx, rows * sy);
    ctx.imageSmoothingEnabled = sx < 1;
    if (e) ctx.drawImage(e.canvas, x0, 0, cols, rows, 0, oy, cols * sx, rows * sy);
    if (liveView()) { ctx.fillStyle = PAL.alive; ctx.fillRect(0, oy + state.layer * rowsPerLayer() * sy - dpr / 2, cw, Math.max(1, dpr)); }
    drawReadback(sx, sy, x0, oy, rows);
    drawHover(sx, sy, x0, oy);
}

function readStripH(sy) { const dpr = window.devicePixelRatio || 1; return state.highlightOut && !isClassic() ? 2 * dpr + Math.max(5 * dpr, sy * 0.8) : 0; }

// The host's read-back of the result: outline each final-row cell it reads and show the value read
// in a strip under the block. Both flash briefly whenever a newly finished cycle is swapped in.
function drawReadback(sx, sy, x0, oy, rows) {
    if (!state.highlightOut || liveView() || state.front.cycle < 0) return;
    const fab = state.fab, evo = state.front.rows[fab.D - 1].evo, dpr = window.devicePixelRatio || 1, now = performance.now();
    if (state.readCycle !== state.front.cycle) { state.readCycle = state.front.cycle; state.readAt = now; }
    const pulse = Math.max(0, 1 - (now - state.readAt) / READ_PULSE_MS);
    if (pulse > 0) state.dirty = true;
    const rowY = oy + (rows - 1) * sy, stripY = oy + rows * sy + 2 * dpr, stripH = readStripH(sy) - 2 * dpr, inv = state.inverted ? 1 : 0;
    const x1 = x0 + fab.W;
    ctx.save();
    ctx.shadowColor = PAL.readback[1]; ctx.shadowBlur = pulse * 14 * dpr;
    ctx.lineWidth = Math.max(1, dpr) * (1 + pulse);
    for (const s of fab.outSrc) {
        if (s < 0 || s + 1 < x0 || s > x1) continue;
        const x = (s - x0) * sx, v = evo[s] ^ inv;
        ctx.fillStyle = PAL.readback[v];
        ctx.fillRect(x, stripY, Math.max(sx, 2 * dpr), stripH);
        if (sx >= 3 * dpr) { ctx.strokeStyle = PAL.readback[1]; ctx.globalAlpha = 0.55 + 0.45 * pulse; ctx.strokeRect(x, rowY, sx, sy); ctx.globalAlpha = 1; }
        if (sx >= 9 * dpr && stripH >= 9 * dpr) {
            ctx.shadowBlur = 0; ctx.fillStyle = v ? '#1c1917' : '#fde68a';
            ctx.font = `${Math.min(stripH, sx) * 0.75}px monospace`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
            ctx.fillText(String(evo[s]), x + sx / 2, stripY + stripH / 2);
            ctx.shadowBlur = pulse * 14 * dpr;
        }
    }
    ctx.restore();
}

function drawHover(sx, sy, x0, oy) {
    const h = state.hover;
    if (!h || h.slot < 0) return;
    const rpl = rowsPerLayer(), dpr = window.devicePixelRatio || 1, rowY = oy + (h.L * rpl + (h.evolved ? rpl - 1 : 0)) * sy;
    ctx.strokeStyle = '#ffffff'; ctx.lineWidth = Math.max(1, dpr);
    ctx.strokeRect((3 * h.slot - x0) * sx, rowY, Math.max(3 * sx, 2), Math.max(sy, 2));
    if (h.evolved || h.L === 0) return;
    const src = state.fab.layers[h.L].src, prevY = oy + ((h.L - 1) * rpl + rpl - 1) * sy;
    ctx.strokeStyle = 'rgba(250, 204, 21, 0.9)';
    for (let p = 0; p < 3; p++) {
        const sIdx = src[3 * h.slot + p];
        if (sIdx < 0) continue;
        ctx.beginPath();
        ctx.moveTo((sIdx + 0.5 - x0) * sx, prevY + sy / 2);
        ctx.lineTo((3 * h.slot + p + 0.5 - x0) * sx, rowY + sy / 2);
        ctx.stroke();
        ctx.strokeRect((sIdx - x0) * sx, prevY, Math.max(sx, 2), Math.max(sy, 2));
    }
}

function rowsForCycle(k) {
    if (k === state.cycle && liveView()) return state.rows;
    if (k === state.front.cycle) return state.front.rows;
    if (state.hoverCycle !== k) { simulateCycle(state.fab, state.cycleInputs[k], state.hoverRows); state.hoverCycle = k; }
    return state.hoverRows;
}

function sigName(x) { const c = state.fab.circuit; return x < 2 ? `const ${x}` : `#${x} ${c.kind[x] === K_IN ? 'input ' + c.label[x] : OP_NAME[c.kind[x]] + (c.label[x] ? ' · ' + c.label[x] : '')}`; }

function updateHover(mx, my) {
    const fab = state.fab;
    state.hover = null;
    if (!fab) return;
    const { sx, sy, rows, cols, x0, oy } = layout(), x = Math.floor(x0 + mx / sx), y = Math.floor((my - oy) / sy), rpl = rowsPerLayer();
    if (mx < 0 || mx >= cols * sx || x >= fab.W || y < 0 || y >= rows) return;
    if (fab.classic) { state.hover = { classic: true, mx, my, r: y, i: x }; return; }
    const k = shownCycle(), L = Math.floor(y / rpl), ly = fab.layers[L];
    state.hover = { mx, my, k, L, evolved: rpl === 1 || y % 2 === 1, slot: x < 3 * ly.n ? (x / 3) | 0 : -1, j: x, computed: k < state.cycle || L < state.layer };
}

function hoverText() {
    const h = state.hover, fab = state.fab;
    if (!h) return null;
    if (h.classic) return classicHoverText();
    const head = `cycle ${h.k} · layer ${h.L + 1}/${fab.D} · ${h.evolved ? 'evolved row (Rule 110 output)' : 'load row (host bus)'}`;
    if (h.slot < 0) return head;
    const ly = fab.layers[h.L], k = ly.op[h.slot], sig = ly.sig[h.slot], p = h.j - 3 * h.slot;
    const v = h.computed ? rowsForCycle(h.k)[h.L][h.evolved ? 'evo' : 'load'][h.j] : '·';
    let what;
    const outs = fab.outIndex.get(sig), outNote = outs ? `\n★ task output bit ${outs.join(', ')}${h.L === fab.D - 1 ? ' — read by the host as the result' : ' — carried down to the last layer'}` : '';
    if (h.evolved) what = p === 1 ? `${OP_NAME[k]} result = ${v} → ${sigName(sig)}${outNote}` : `by-product cell = ${v} (never read)`;
    else {
        const role = k === K_BUF ? ['rail 0', 'signal', 'rail 0'] : k === K_NAND ? ['a', 'rail 1 (opcode NAND)', 'b'] : [k === K_OR ? 'rail 0 (opcode OR)' : 'rail 1 (opcode XOR)', 'a', 'b'];
        const s = ly.src[h.j], from = s >= 0 ? `← cell ${s} of layer ${h.L}` : s <= -3 ? `← ${sigName(fab.circuit.inputs[-3 - s])}` : '(constant rail)';
        what = `${OP_NAME[k]} slot ${h.slot}: ${role[p]} = ${v} ${from}`;
    }
    return `${head}\ncell ${h.j} · ${what}`;
}

function speedFromSlider(x) { return Math.max(1, Math.round(10 ** (x / 100 * 3.7))); }

function updateReadouts() {
    const t = state.task, fab = state.fab;
    $('stat-cycle').textContent = state.cycle;
    $('stat-layer').textContent = fab ? `${state.layer}/${fab.D}` : '0';
    const out = $('output');
    if (state.error) { out.textContent = state.error; out.classList.add('error'); }
    else { out.classList.remove('error'); out.textContent = t ? t.report(state) : '—'; }
    drawOutPlot();
    if (!fab) { $('diagnostics').textContent = '—'; return; }
    const btnState = () => {
        $('btn-play').disabled = state.playing || state.done; $('btn-pause').disabled = !state.playing;
        for (const id of ['btn-step-layer', 'btn-step-cycle', 'btn-run-end']) $(id).disabled = state.done || state.playing;
        $('btn-run-end').textContent = state.turbo ? 'Running…' : 'Run to end';
    };
    if (fab.classic) {
        $('diagnostics').textContent = [
            `task        ${t.title}`,
            `engine      pure Rule 110 - no host, no circuit, no wiring`,
            `edges       ${t.wrap ? 'wrap around (ring)' : 'dead cells beyond both edges'}`,
            `rows        ${t.gen}/${t.G} computed`,
            `R110 updates ${state.cells}`,
            `ether test  7×3 neighbourhood vs the 14-cell ether`,
        ].join('\n');
        return btnState();
    }
    const c = fab.counts, fmt = n => n >= 1e9 ? (n / 1e9).toFixed(2) + 'G' : n >= 1e6 ? (n / 1e6).toFixed(2) + 'M' : n >= 1e4 ? (n / 1e3).toFixed(1) + 'k' : String(n);
    const perCycle = fab.layers.reduce((a, l) => a + 3 * l.n, 0);
    $('diagnostics').textContent = [
        `task        ${t.title}`,
        `gates       NAND ${c[K_NAND]} · OR ${c[K_OR]} · XOR ${c[K_XOR]}`,
        `wire slots  ${c[K_BUF]} (buffer triples)`,
        `inputs      ${fab.nIn} bits → outputs ${fab.outIds.length} bits`,
        `layers      ${fab.D} per cycle (= Rule 110 generations)`,
        `row width   ${fab.W} cells max (${fab.layout} layout)`,
        `cells/cycle ${fmt(perCycle)}`,
        `R110 updates ${fmt(state.cells)}`,
        `fabric ≡ circuit   ${state.fabricFail >= 0 ? '✗ mismatch at cycle ' + state.fabricFail : state.fabricOk ? '✓ ' + state.fabricOk + ' cycle(s)' : '—'}`,
        `circuit ≡ task     ${t.refLine()}`,
    ].join('\n');
    const btnPlay = $('btn-play'), btnPause = $('btn-pause');
    btnPlay.disabled = state.playing || state.done; btnPause.disabled = !state.playing;
    for (const id of ['btn-step-layer', 'btn-step-cycle', 'btn-run-end']) $(id).disabled = state.done || state.playing;
    $('btn-run-end').textContent = state.turbo ? 'Running…' : 'Run to end';
}

let lastTip = [0, 0];
function refreshTooltip() { updateTooltip(...lastTip); }
function updateTooltip(cx, cy) {
    if (cx !== undefined) lastTip = [cx, cy];
    const tip = $('tooltip'), ht = hoverText();
    tip.classList.toggle('hidden', !ht);
    if (!ht) return;
    tip.textContent = ht;
    const r = container.getBoundingClientRect(), w = tip.offsetWidth, h = tip.offsetHeight;
    let x = cx - r.left + 16, y = cy - r.top + 16;
    if (x + w > r.width - 8) x = cx - r.left - w - 16;
    if (y + h > r.height - 8) y = cy - r.top - h - 16;
    tip.style.left = `${Math.max(4, x)}px`; tip.style.top = `${Math.max(4, y)}px`;
}

function updateStatus() {
    const bar = $('status-bar');
    if (state.error) { bar.textContent = 'Compile error — see Output'; return; }
    if (!state.fab) { bar.textContent = 'No task compiled'; return; }
    if (isClassic()) {
        const t = state.task, z = state.zoom;
        bar.textContent = `${state.done ? 'Done' : state.playing ? 'Running' : 'Ready'} · classic free run · generation ${t.gen - 1}/${t.gens} · cells ${Math.floor(z.x0)}–${Math.min(t.W, Math.ceil(z.x0 + z.cells)) - 1} of ${t.W} (scroll to zoom)`;
        return;
    }
    const k = shownCycle(), inp = state.cycleInputs[k], label = inp ? ` · ${state.task.cycleLabel(inp)}` : '';
    const z = state.zoom, view = `cells ${Math.floor(z.x0)}–${Math.min(state.fab.W, Math.ceil(z.x0 + z.cells)) - 1} of ${state.fab.W} (scroll to zoom)`;
    bar.textContent = state.done ? `Done · ${state.cycle} cycle(s) · showing cycle ${k}${label} · ${view}` : `${state.playing ? 'Running' : 'Ready'} · cycle ${k}${label} · layer ${state.layer}/${state.fab.D} · ${view}`;
}

function compile() {
    const kind = $('select-task').value;
    state.error = null;
    try {
        let task;
        if (kind === 'script') {
            $('compiled-asm').textContent = '';
            try { task = makeScriptTask($('input-script').value, Math.max(1, parseInt($('input-max-cycles-script').value, 10) || 1)); }
            finally { const asm = task ? task.asm : null; $('compiled-asm').textContent = asm || ''; $('compiled-size').textContent = task ? task.size : '—'; }
        }
        else if (kind === 'cpu') task = makeCpuTask($('input-program').value, Math.max(1, parseInt($('input-max-cycles').value, 10) || 1));
        else if (kind === 'arith') task = makeArithTask($('select-op').value, +$('select-bits').value, Number($('input-a').value), Number($('input-b').value));
        else if (kind === 'classic') task = makeClassicTask({
            width: parseInt($('input-classic-width').value, 10), gens: parseInt($('input-classic-gens').value, 10),
            start: $('select-classic-start').value, pattern: $('input-classic-pattern').value,
            density: +$('input-classic-density').value, wrap: $('select-classic-edge').value === 'wrap',
        });
        else task = makeExprTask($('input-expr').value);
        setTask(task);
        state.plotNames = task.type === 'cpu' ? plotNames() : null;
        state.outFormat = task.type === 'cpu' ? outFormat() : null;
    } catch (err) {
        state.error = err.message;
        if (err.asm) $('compiled-asm').textContent = err.asm;
        state.task = state.fab = null; state.dirty = true;
    }
    updateReadouts(); updateStatus();
}

// examples may contain $RAND: each Load replaces every one with a fresh random byte
const withRandoms = text => text.replace(/\$RAND/g, () => Math.floor(Math.random() * 256));

// ---------------------------------------------------------------- OUT plot
// A "plot: a, b" comment in the program names the series; OUT values are dealt to them in turn.

const PLOT_COLORS = ['#0284c7', '#ec4899'];
let plotState = { key: '', hover: -1 };
function plotNames() {
    const src = $('select-task').value === 'script' ? $('input-script').value : $('input-program').value;
    const m = /(?:\/\/|;|#)\s*plot:\s*([^\n]+)/i.exec(src);
    return m ? m[1].split(',').map(x => x.trim()).filter(Boolean).slice(0, PLOT_COLORS.length) : ['OUT'];
}
// an "out: u16" comment means OUT bytes come in (high, low) pairs that form 16-bit numbers
function outFormat() {
    const src = $('select-task').value === 'script' ? $('input-script').value : $('input-program').value;
    return /(?:\/\/|;|#)\s*out:\s*u16\b/i.test(src) ? 'u16' : null;
}
const pairU16 = out => { const v = []; for (let i = 0; i + 1 < out.length; i += 2) v.push(out[i] * 256 + out[i + 1]); return v; };

function drawOutPlot(force) {
    const cv = $('out-plot'), t = state.task, raw = t && !state.error && Array.isArray(t.out) ? t.out : null;
    const u16 = state.outFormat === 'u16', out = raw && u16 ? pairU16(raw) : raw, vmax = u16 ? 65535 : 255;
    cv.classList.toggle('hidden', !out || out.length < 2);
    if (!out || out.length < 2) return;
    const names = state.plotNames || ['OUT'], k = names.length, key = `${out.length}|${names}|${plotState.hover}|${cv.clientWidth}`;
    if (!force && key === plotState.key) return;
    plotState.key = key;
    const dpr = window.devicePixelRatio || 1, w = cv.clientWidth, h = cv.clientHeight, g = cv.getContext('2d');
    cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr); g.setTransform(dpr, 0, 0, dpr, 0, 0);
    g.clearRect(0, 0, w, h);
    const padL = u16 ? 38 : 26, padR = 6, padT = k > 1 ? 18 : 6, padB = 17, n = Math.ceil(out.length / k);
    plotState.padL = padL;
    const X = i => padL + (n > 1 ? i / (n - 1) : 0.5) * (w - padL - padR), Y = v => padT + (1 - v / vmax) * (h - padT - padB);
    g.font = '9px monospace'; g.textBaseline = 'middle'; g.textAlign = 'right';
    for (const v of u16 ? [0, 32768, 65535] : [0, 128, 255]) { g.strokeStyle = v === (u16 ? 32768 : 128) ? '#334155' : '#1e293b'; g.lineWidth = 1; g.beginPath(); g.moveTo(padL, Y(v) + 0.5); g.lineTo(w - padR, Y(v) + 0.5); g.stroke(); g.fillStyle = '#64748b'; g.fillText(String(v), padL - 4, Y(v)); }
    g.textAlign = 'left'; g.fillText(`${n} value${n > 1 ? 's' : ''}${k > 1 ? ' each' : ''}`, padL, h - 7);
    names.forEach((name, sI) => {
        const pts = []; for (let i = sI; i < out.length; i += k) pts.push(out[i]);
        g.strokeStyle = PLOT_COLORS[sI]; g.lineWidth = 2; g.lineJoin = 'round'; g.beginPath();
        pts.forEach((v, i) => i ? g.lineTo(X(i), Y(v)) : g.moveTo(X(i), Y(v))); g.stroke();
        if (pts.length <= 40) { g.fillStyle = PLOT_COLORS[sI]; for (let i = 0; i < pts.length; i++) { g.beginPath(); g.arc(X(i), Y(pts[i]), 2.5, 0, 7); g.fill(); } }
        if (k > 1) { const lx = padL + sI * 70; g.fillStyle = PLOT_COLORS[sI]; g.fillRect(lx, 5, 10, 3); g.fillStyle = '#cbd5e1'; g.fillText(name, lx + 14, 7); }
    });
    const i = plotState.hover;
    if (i >= 0 && i < n) {
        g.strokeStyle = '#94a3b8'; g.lineWidth = 1; g.beginPath(); g.moveTo(X(i) + 0.5, padT); g.lineTo(X(i) + 0.5, h - padB); g.stroke();
        const vals = names.map((name, sI) => { const v = out[i * k + sI]; return v === undefined ? null : `${name} ${v}`; }).filter(Boolean);
        names.forEach((_, sI) => { const v = out[i * k + sI]; if (v === undefined) return; g.fillStyle = '#0f172a'; g.beginPath(); g.arc(X(i), Y(v), 4.5, 0, 7); g.fill(); g.fillStyle = PLOT_COLORS[sI]; g.beginPath(); g.arc(X(i), Y(v), 3, 0, 7); g.fill(); });
        const label = `#${i}  ${vals.join('  ')}`, tw = g.measureText(label).width + 8, lx = Math.min(Math.max(padL, X(i) - tw / 2), w - padR - tw);
        g.fillStyle = 'rgba(15, 23, 42, 0.92)'; g.fillRect(lx, padT, tw, 14); g.fillStyle = '#e2e8f0'; g.fillText(label, lx + 4, padT + 7);
    }
}

function showTaskPanel() { for (const k of ['script', 'cpu', 'arith', 'expr', 'classic']) $(`panel-${k}`).classList.toggle('hidden', $('select-task').value !== k); }

function buildRuleWidgets() {
    const table = $('rule-table');
    for (let i = 7; i >= 0; i--) {
        const d = document.createElement('div'); d.className = 'rule-case';
        const trio = document.createElement('div'); trio.className = 'trio';
        for (let b = 2; b >= 0; b--) { const s = document.createElement('span'); if ((i >> b) & 1) s.className = 'on'; trio.appendChild(s); }
        const o = document.createElement('span'); if (RULE_TABLE[i]) o.className = 'on';
        d.append(trio, o); table.appendChild(d);
    }
    // Gate triples: one aligned row per gate - name and pattern, then every input case drawn as
    // the three load cells -> the evolved centre cell in the canvas's Roles colours. The results
    // are read from RULE_TABLE, so the legend is the rule itself, not a hand-written table.
    const cell = c => `<span class="cell" style="background:${c}"></span>`;
    const GATES = [
        { k: K_NAND, name: 'NAND', pat: '[a,<b>1</b>,b]', triple: (a, b) => [a, 1, b], rail: [1] },
        { k: K_OR, name: 'OR', pat: '[<b>0</b>,a,b]', triple: (a, b) => [0, a, b], rail: [0] },
        { k: K_XOR, name: 'XOR', pat: '[<b>1</b>,a,b]', triple: (a, b) => [1, a, b], rail: [0] },
        { k: K_BUF, name: 'wire', pat: '[<b>0</b>,a,<b>0</b>]', triple: a => [0, a, 0], rail: [0, 2] },
    ];
    $('gate-legend').innerHTML = GATES.map(g => {
        const combos = g.k === K_BUF ? [[0], [1]] : [[0, 0], [0, 1], [1, 0], [1, 1]];
        const cases = combos.map(ab => {
            const t = g.triple(...ab), v = RULE_TABLE[(t[0] << 2) | (t[1] << 1) | t[2]];
            const inputs = g.k === K_BUF ? `a=${ab[0]}` : `a=${ab[0]} b=${ab[1]}`;
            return `<span class="case" title="${inputs}: cells ${t.join(' ')} → rule 110 case ${t.join('')} → ${v}">` +
                `<span class="cells">${t.map((x, p) => cell((g.rail.includes(p) ? PAL.rail : PAL.oper)[x])).join('')}<span class="arrow">→</span>${cell(PAL.res[g.k][v])}</span>` +
                `<span class="ab">${ab.join('')}</span></span>`;
        }).join('');
        return `<div class="gate-row"><div class="gate-name"><i style="background:${PAL.res[g.k][1]}"></i>${g.name}<span class="gate-pat">${g.pat}</span></div><div class="gate-cases">${cases}</div></div>`;
    }).join('');
    const key = (label, ...cols) => `<div class="key">${cols.map(c => `<i style="background:${c}"></i>`).join('')}<span>${label}</span></div>`;
    $('colour-key').innerHTML = [
        key('NAND result', ...[...PAL.res[K_NAND]].reverse()), key('operand a, b', ...[...PAL.oper].reverse()),
        key('OR result', ...[...PAL.res[K_OR]].reverse()), key('rail (constant)', ...[...PAL.rail].reverse()),
        key('XOR result', ...[...PAL.res[K_XOR]].reverse()), key('by-product', PAL.spill[1]),
        key('wire result', ...[...PAL.res[K_BUF]].reverse()), key('output bit', ...[...PAL.out].reverse()),
        key('read back', ...[...PAL.readback].reverse()),
    ].join('');
}

function setupEvents() {
    $('select-task').onchange = () => { showTaskPanel(); compile(); };
    $('btn-load-program').onclick = () => { $('input-program').value = withRandoms(PROGRAMS[$('select-program').value]); compile(); };
    $('btn-load-script').onclick = () => { $('input-script').value = withRandoms(SCRIPTS[$('select-script').value]); compile(); };
    for (const id of ['select-classic-start', 'select-classic-edge', 'input-classic-width', 'input-classic-gens', 'input-classic-pattern', 'input-classic-density']) $(id).onchange = compile;
    $('select-classic-style').onchange = e => { state.classicStyle = e.target.value; invalidatePaint(); };
    $('btn-load-expr').onclick = () => { $('input-expr').value = EXPRS[$('select-expr').value]; compile(); };
    $('select-op').onchange = $('select-bits').onchange = compile;
    $('btn-compile').onclick = compile;
    const plot = $('out-plot');
    plot.addEventListener('mousemove', e => {
        const t = state.task, k = (state.plotNames || ['OUT']).length; if (!t || !t.out) return;
        const len = state.outFormat === 'u16' ? pairU16(t.out).length : t.out.length, pl = plotState.padL || 26;
        const n = Math.ceil(len / k), r = plot.getBoundingClientRect(), x = e.clientX - r.left;
        plotState.hover = n > 1 ? Math.max(0, Math.min(n - 1, Math.round((x - pl) / (r.width - pl - 6) * (n - 1)))) : 0; drawOutPlot();
    });
    plot.addEventListener('mouseleave', () => { plotState.hover = -1; drawOutPlot(); });
    $('select-layout').onchange = e => { fabricLayout = e.target.value; compile(); };
    $('btn-play').onclick = () => { if (!state.done && state.fab) { state.playing = true; state.liveStep = false; updateReadouts(); } };
    $('btn-pause').onclick = () => { state.playing = state.turbo = false; updateReadouts(); updateStatus(); };
    $('btn-reset').onclick = () => { resetRun(); updateReadouts(); updateStatus(); };
    $('btn-step-layer').onclick = () => { state.liveStep = true; stepLayer(); afterStep(); };
    $('btn-step-cycle').onclick = () => { state.liveStep = false; stepCycle(); afterStep(); };
    $('btn-run-end').onclick = () => { if (!state.done && state.fab) { state.playing = state.turbo = true; state.liveStep = false; updateReadouts(); } };
    const speed = $('input-speed');
    speed.oninput = () => { state.speed = speedFromSlider(+speed.value); $('speed-value').textContent = `${state.speed} layer${state.speed > 1 ? 's' : ''}/frame`; };
    speed.oninput();
    $('select-color-mode').onchange = e => { state.colorMode = e.target.value; invalidatePaint(); };
    $('input-show-load').onchange = e => { state.showLoad = e.target.checked; state.hover = null; if (state.fab) clampView(); invalidatePaint(); };
    $('input-highlight-out').onchange = e => { state.highlightOut = e.target.checked; if (state.fab) clampView(); invalidatePaint(); };
    $('btn-invert').onclick = () => { state.inverted = !state.inverted; invalidatePaint(); };

    const pos = e => { const r = canvas.getBoundingClientRect(), dpr = window.devicePixelRatio || 1; return [(e.clientX - r.left) * dpr, (e.clientY - r.top) * dpr]; };
    // right or middle button drag pans; panMask is that button's bit in MouseEvent.buttons
    let panning = null, panMask = 0;
    const PAN_MASK = { 1: 4, 2: 2 };
    const endPan = () => { panning = null; panMask = 0; container.classList.remove('panning'); };
    canvas.addEventListener('contextmenu', e => e.preventDefault());
    canvas.addEventListener('auxclick', e => { if (e.button === 1) e.preventDefault(); });
    canvas.addEventListener('mousedown', e => { if (PAN_MASK[e.button] && state.fab) { e.preventDefault(); panning = pos(e); panMask = PAN_MASK[e.button]; container.classList.add('panning'); } });
    window.addEventListener('mouseup', e => { if (panning && PAN_MASK[e.button] === panMask) endPan(); });
    window.addEventListener('mousemove', e => {
        const p = pos(e);
        if (panning && !(e.buttons & panMask)) endPan();
        if (panning) { panBy(p[0] - panning[0], p[1] - panning[1]); panning = p; }
        const had = state.hover;
        if (e.target === canvas) updateHover(p[0], p[1]); else state.hover = null;
        if (had || state.hover) state.dirty = true;
        updateTooltip(e.clientX, e.clientY);
    });
    container.addEventListener('wheel', e => {
        if (!state.fab) return;
        e.preventDefault();
        const p = pos(e);
        zoomAt(e.deltaY > 0 ? 1.15 : 0.87, p[0], p[1]);
        updateHover(p[0], p[1]); updateTooltip(e.clientX, e.clientY); updateStatus();
    }, { passive: false });
    canvas.addEventListener('mouseleave', () => { state.hover = null; state.dirty = true; updateTooltip(); });
    window.addEventListener('resize', resizeCanvas);
    window.addEventListener('keydown', e => {
        if (['INPUT', 'SELECT', 'TEXTAREA'].includes(document.activeElement?.tagName) || e.ctrlKey || e.metaKey || e.altKey) return;
        const k = e.key.toLowerCase();
        if (k === ' ') { e.preventDefault(); (state.playing ? $('btn-pause') : $('btn-play')).click(); }
        else if (k === 'n' && !state.playing) $('btn-step-layer').click();
        else if (k === 'c' && !state.playing) $('btn-step-cycle').click();
        else if (k === 'i') $('btn-invert').click();
    });
}

function afterStep() { state.hoverCycle = -1; if (state.hover) { updateHover(state.hover.mx, state.hover.my); refreshTooltip(); } state.dirty = true; updateReadouts(); updateStatus(); }

function tick() {
    if (state.playing) {
        const t0 = performance.now(), budget = state.turbo ? 40 : 12;
        let n = state.turbo ? Infinity : state.speed;
        while (n-- > 0 && !state.done) { stepLayer(); if (performance.now() - t0 > budget) break; }
        afterStep();
    }
    if (state.dirty) { state.dirty = false; draw(); }
    requestAnimationFrame(tick);
}

function init() {
    canvas = $('viewport'); ctx = canvas.getContext('2d'); container = $('viewport-container');
    buildColors(); buildRuleWidgets(); setupEvents(); resizeCanvas();
    $('input-program').value = PROGRAMS.fib;
    $('input-script').value = SCRIPTS.fib;
    $('input-expr').value = EXPRS.adder;
    showTaskPanel();
    compile();
    requestAnimationFrame(tick);
}

if (typeof document !== 'undefined') init();
