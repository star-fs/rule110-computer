# Rule 110 Computer

An experimental computer in which every logic gate is a single **Rule 110** cell
update. You write a program (in a small JavaScript-style language or in
assembly), it runs on an 8-bit CPU with RAM, and that CPU is built entirely out
of Rule 110 generations. The canvas shows the resulting spacetime diagram.

It is a sibling of n-sides-GOL and the Hat Fractal Explorer and uses the same UI.

## Running it

No build step and no dependencies. Open `index.html` directly, or serve the folder:

```
python3 -m http.server 8935
```

then browse to `http://127.0.0.1:8935/`.

**Quick start:** the app opens on the Script task with the Fibonacci example.
Press **Run to end**, then hover the canvas. For something bigger, pick
*Bubble sort of 8 (array in RAM)* → **Load** → **Run to end**.

## How it computes

Rule 110's local rule is `f(l, c, r) = l ? (c XOR r) : (c OR r)`. Put a constant
in one slot of a three-cell group, and the centre cell's next state becomes a
logic gate. Which slot holds the constant acts as the opcode:

| load triple | next centre cell |
|-------------|------------------|
| `[a, 1, b]` | NAND(a, b)       |
| `[0, a, b]` | OR(a, b)         |
| `[1, a, b]` | XOR(a, b)        |
| `[0, a, 0]` | a (wire / buffer) |

The pipeline:

1. **Compile.** The task becomes a combinational circuit of NAND/OR/XOR gates.
   The builder merges duplicate gates and folds constants, but never folds task
   inputs.
2. **Schedule.** Gates are levelled into *layers*. A signal needed several
   layers later is carried down by wire triples.
3. **Execute.** For each layer, the host writes a *load row* by copying bits from
   the previous layer's *evolved row* (a fixed wiring table), inserts input bits,
   and adds the constant rails. Then **one plain Rule 110 generation** is applied
   to the whole row. The host never computes anything; every logic operation is
   that Rule 110 step.
4. **Clock** (CPU task). One cycle is one pass through all layers. The host
   latches the next-state outputs (registers, program counter, RAM) and feeds
   them back as the next cycle's inputs. These latches are the CPU's flip-flops.

### Fabric layout

**Fabric layout** (in the Task section) chooses how gates are placed into
layers. Both options are pure wiring and give the same depth.

- **Compact** (default):
  - Each input bit is loaded in the layer that first uses it.
  - Gates are placed as late as their consumers allow.
  - A balancing pass then keeps the widest layer as narrow as possible. It works
    back from the last layer and, under a width cap, decides whether each gate is
    computed in this layer or carried one more layer on a wire. It keeps the
    narrowest result. Without this pass, the 128 RAM write-backs all land in one
    layer.
- **Original:** every input enters at layer 1, and every gate is placed as early
  as possible.

For the default CPU (64 instructions / 16 bytes):

| Layout   | Row width   | Wire slots | Cells per cycle |
|----------|-------------|------------|-----------------|
| Compact  | 729 cells   | 1,870      | 19.5k           |
| Original | 3,600 cells | 10,349     | 44.9k           |

## The CPU

| | |
|---|---|
| Data | 8-bit, 4 registers `r0`–`r3`, reach-around arithmetic |
| CPU size | selectable: ROM 32 / 64 / 128 instructions, RAM 16 or 32 bytes |
| Circuit | size-dependent, see the table below |

The ROM is fed in as input bits every cycle, so the circuit is the same for
every program of a given size.

**CPU size.** The ROM and RAM selectors (next to *Fabric layout*) choose the
CPU's dimensions. Changing them rebuilds the circuit: a bigger ROM widens the
PC and the ROM mux, and 32-byte RAM adds a fifth bit to the memory offset.
Programs that no longer fit (too many instructions, offsets or arrays past the
RAM end) are rejected at compile time. Measured with the compact layout:

| ROM | RAM | Gates | Layers | Row width | Cells/cycle | Input bits |
|-----|-----|-------|--------|-----------|-------------|------------|
| 32  | 16  | 3,088 | 45 | 573  | 17.0k | 678  |
| 64  | 16  | 4,634 | 47 | 729  | 19.5k | 1,191 |
| 128 | 16  | 7,716 | 49 | 1,341 | 28.9k | 2,216 |
| 32  | 32  | 3,969 | 45 | 969  | 23.2k | 806  |
| 64  | 32  | 5,515 | 47 | 975  | 28.0k | 1,319 |
| 128 | 32  | 8,597 | 49 | 1,446 | 32.9k | 2,344 |

The default 64-instruction / 16-byte CPU is the original one: 4,634 gates
(4,492 NAND, 92 OR, 50 XOR), 47 layers, 729 cells wide, 1,191 input bits per
cycle.

### Instruction set

| Instruction | Effect |
|---|---|
| `HALT` | stop |
| `NOP` | no operation (`MOV r0, r0`) |
| `LDI rd, imm` | `rd = imm` |
| `MOV rd, rs` | `rd = rs` |
| `ADD` / `SUB` / `AND` / `OR` / `XOR rd, rs` | `rd = rd op rs` |
| `SHL rd` / `SHR rd` | shift by 1 (`SHL` is shorthand for `ADD rd, rd`) |
| `ADDI rd, imm` | `rd = rd + imm` (imm −128..255) |
| `LD rd, [rs+k]` / `ST rd, [rs+k]` | load / store `RAM[(rs + k) mod RAM]`, k = 0..15 (16-byte) or 0..31 (32-byte) |
| `LD rd, [k]` / `ST rd, [k]` | load / store a fixed address |
| `JMP label` | jump |
| `JZ` / `JNZ rd, label` | jump if `rd` is zero / non-zero |
| `JLT rd, rs, label` | jump if `rd < rs` (unsigned) |
| `OUT rd` | append `rd` to the output |
| `.data 1, 2, 3` | preload RAM from address 0 |

Labels are `name:`, and comments start with `;` or `#`. The memory
instruction took over the opcode `SHL` used to have.

**RAM.** RAM is stored exactly like the registers: the host latches its 128
(16-byte) or 256 (32-byte) bits between cycles. The address adder, the
16-/32-way read selector and the write-back of every byte are computed in the
fabric.

## The script language

A C/JavaScript-style language, chosen because it is the cheapest modern syntax to
parse (no indentation rules, no types). It compiles to the assembly above, and
the compiled listing is shown beside the script.

```js
let a = [5, 3, 9, 1];            // array in RAM
let buf[8];                      // 8 zero bytes
let n = 4, i, x, y;
for (i = 0; i < n; i++) out(a[i]);
while (n != 1) {
    n--;
    for (i = 0; i < n; i++) {
        x = a[i]; y = a[i + 1];
        if (y < x) { a[i] = y; a[i + 1] = x; }
    }
}
```

**Supported:**
- declarations: `let` / `var` / `const`, including several at once
- assignment: `=`, `+= -= &= |= ^= <<= >>=`, `++`, `--`
- control flow: `if`/`else`, `while`, `for`, `break`, `continue`
- `out(expr)` and `halt()`
- operators on 8-bit values: `+ - & | ^ ~ << >>`
- unsigned comparisons `< > <= >= == !=`, and `&& || !`
- `true`/`false`, hex `0x…` and binary `0b…` literals, `//` and `/* */` comments

**Arrays.** Declare them with `let v = [1, 2, 3];` (constant values) or
`let v[8];` (zeros). Use them as `v[i]`, `v[i + 1] = x`, `v[i] += 2` and
`v[i]++`. A constant offset such as `i + 1` goes straight into the instruction's
offset. There is no bounds checking: addresses wrap at the RAM size (16 or 32).

**Where values live:**
- Arrays are laid out in RAM from address 0.
- Scalar variables go in registers, most-used first. Uses inside loops count 8×
  per nesting level.
- Registers left over are scratch space for evaluating expressions.
- Extra variables, or variables moved out to free a register, live in RAM after
  the arrays.
- The compiler tries every way of splitting variables between registers and RAM
  and keeps the shortest program. The listing's first line says where everything
  went.

**Hardware limits:**
- There are no multiply or divide instructions, so `*` works only with a
  constant power of two, and `/` and `%` need a loop.
- There are no functions.
- Everything must fit in the selected ROM (32–128 instructions) and RAM
  (16 or 32 bytes): arrays plus spilled variables.

**Code generation:** loops are emitted with the test at the bottom, so every
condition needs only a "jump if true". Jumps to the very next instruction are
removed.

## Examples

`$RAND` in an example is replaced by a fresh random byte each time you press
Load.

Examples come in two sets, chosen by the selected **RAM size**: with 16-byte
RAM the smaller data is used, and switching to 32-byte RAM substitutes the
doubled versions (bigger arrays, stacks and spills that fill the extra room).
Pressing **Load** always substitutes the version that matches the current RAM
size; changing the size re-substitutes an example that is still loaded. A few
of the larger ones — the sieve's 32 flags and the 20-element reversal — need
the 32-byte CPU and won't compile on the 16-byte one.

**Script** (18): 16-bit Fibonacci, multiply by shift-and-add, GCD, primes below 40,
countdown, Collatz, bubble sort of 8/16 in a RAM array, sieve of Eratosthenes
(primes < 16 / < 32), reverse an array of 10/20, running totals over 8/16
elements, a stack of 8/16 (push then pop), 8/12 variables spilling to RAM,
bubble sort of 4 in registers, sine & cosine, random numbers (LCG),
divide with remainder, integer square root, and counting 1 bits.

**Assembly** (10): 16-bit Fibonacci, multiply, GCD, primes, countdown, bubble sort of 4
(XOR swaps), sine & cosine, random numbers, bubble sort of 8/16 with `LD`/`ST`,
and an array sum of 8/16 with `.data`.

**16-bit Fibonacci** runs on the 8-bit CPU by keeping each number as two bytes
and carrying from the low byte into the high byte by hand. It prints all 25
Fibonacci numbers below 65,536, ending at 46,368.

**Sine & cosine** uses Minsky's circle algorithm (HAKMEM item 149):
`cos -= sin/8; sin += cos/8`, with only shifts and adds. Values are stored as
128 + v, so that an unsigned shift followed by `+64` is a signed shift.

## Other tasks

- **Arithmetic:** A + B, A − B, A × B (array multiplier), AND/OR/XOR, A < B,
  A == B and max, with 4-, 8-, 12- or 16-bit operands.
- **Boolean expressions:** named expressions over up to 6 variables. Every
  truth-table row runs as a parallel lane in a single pass.
- **Classic free run:** the textbook spacetime diagram, with Rule 110 running on
  its own and no host, circuit or wiring.
  - The defaults (257 cells, one live cell at the right edge, 256 generations,
    dead cells beyond the edges) reproduce Wikipedia's *Sample run of Rule 110*
    image cell for cell.
  - The start row can also be a centred cell, a random row, the ether, or a
    custom 0/1 pattern, and the edges can wrap around.
  - Styles: *Classic* (black on grey); *Gliders highlighted*, which compares each
    cell's 7×3 neighbourhood with Cook's 14-cell ether (`11111000100110`), dims
    ether cells and shows gliders and collisions in rose; and *App colours*.
  - Hovering shows a cell's three parent cells and the rule case that produced
    it.

## Using the canvas

- **One cycle at a time.** While playing, the display is double-buffered: each
  cycle is computed off-screen and appears only once all its layers are done.
  **Step layer** shows the current cycle filling in one layer at a time.
- **View:**
  - Each layer shows its load row and its evolved row.
  - It opens on the first 600 cells across the full width (or the whole row, if
    narrower), with every layer stacked from the top.
  - Cells are always square.
- **Zoom and pan:**
  - The scroll wheel zooms around the cursor, from about 30 cells across out to
    the full layer width. Classic free run can zoom out further, until the whole
    run fits.
  - Dragging with the right or middle mouse button pans horizontally and
    vertically, stopping at the edges.
- **Hover** a cell for a tooltip with its layer, role, value and the signal it
  carries. On a load row it also draws the host's wire back to the source cell.
  A classic run shows parents and structure instead.
- **Keys:** Space play/pause · N step layer · C step cycle · I invert colours.

### Rendering

- **The Rule legend** (sidebar) has three labelled parts:
  - the 8 Rule 110 cases, (left, centre, right) → new centre
  - a *gate triples* table: one row per gate (NAND, OR, XOR, wire) with its
    pattern and every input case, drawn as the three load cells → the evolved
    centre cell and labelled with its `ab` inputs. The results are read from the
    rule table itself. Hover a case for details, e.g.
    `a=1 b=1: cells 1 1 1 → rule 110 case 111 → 0`.
  - a two-column *canvas colours* key, showing both shades (1 bright, 0 dark)
    wherever both appear.
- **Roles** colours:
  - constant rails (the opcodes): amber
  - operands: blue
  - results by gate type: NAND green, OR violet, XOR pink, wire sky
  - by-product cells the host never reads: dark grey
- **Raw** colours show plain live/dead cells.
- **Output cells**:
  - Bits that are task outputs are red: bright for 1, dark for 0. That includes
    each output bit where it is computed and on its wires down to the last layer.
  - In the last layer, the cells the host reads are also outlined in yellow.
  - A read-back strip under the block shows each value read, with digits when
    zoomed in.
  - The outlines and strip flash each time a cycle's result is read back.
- **Show load rows** off shows only the Rule 110 outputs. **Invert** swaps live and
  dead colours for display only.

### Output panel

- **CPU and script tasks** show:
  - the program counter and next instruction
  - the registers, and variables by name
  - array contents
  - all RAM bytes (16 or 32), with the last byte written marked `*`
  - the OUT list
- **OUT plot:** a small line chart of the OUT values. A `plot: sin, cos` comment
  in the program splits the alternating outputs into named series with a
  legend. Hover it to read off values.
- **16-bit output:** an `out: u16` comment means OUT bytes come in (high, low)
  pairs. The Output list and the plot then show them as 16-bit numbers, with
  the plot scaled 0–65535.

## Verification

The Diagnostics panel runs two independent checks on every cycle:

- **fabric ≡ circuit:** the Rule 110 fabric's outputs match a direct evaluation of
  the gate circuit.
- **circuit ≡ task:** the results match a separate JavaScript reference: a CPU
  emulator stepped in lockstep (registers, PC, output and every RAM byte),
  JavaScript arithmetic, or JavaScript expression evaluation.

During development, all 28 examples and fuzzed random programs were run through
the fabric: random instruction streams exercising every LD/ST addressing mode,
and compiled scripts checked against a separate interpreter.

## Honest limits

This is a Rule 110 *gate fabric*. It is not Cook's glider-collision universality
construction:

- Routing between layers is a fixed wire table applied by the host.
- The CPU's registers and RAM are latched by the host between cycles.

Every logic operation, though, is computed by Rule 110 itself. Classic free run
shows the other side: Rule 110 alone, with gliders moving through the ether.

## Files

- `index.html`: layout and controls
- `style.css`: styles (shared look with the sibling apps)
- `app.js`: everything else: circuit builder, fabric scheduler, Rule 110
  engine, CPU, assembler, script compiler, classic free run and rendering.
  There is no build step, and no modules.

&copy;opyleft 2026 star morin
