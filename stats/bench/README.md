# Statistics benchmark

This times the mean, sample variance, median, and a 100-bin histogram of 10000 doubles. It also times U32 gcd, checked lcm, and integer square root. It compares `stats` with C, Rust, Python, and JavaScript.

## Run

```sh
python3 run.py      # 3 runs, median
python3 run.py 5    # 5 runs
```

You need `bend`, `cc`, `rustc`, `bun`, `node`, and `python3`. Binaries go to `out/`, which git ignores. Each invocation builds each native program once. It checks a small integer input before the full input. It exits non-zero if a build fails, if checksums change between runs, or if two programs disagree on a checksum.

## The work

Each program makes 10000 xorshift32 draws from seed 44 and shifts each draw right by 12 bits, so every value is an integer below 2^20 and exact as a double. Each op prints the xor of the two words of its result.

| op | C | Rust | Python | JavaScript | Bend |
|---|---|---|---|---|---|
| mean | loop | `Iterator::sum` | `statistics.fmean` | loop | `Stats.mean` |
| variance | two-pass loop | two-pass `sum` | two-pass loop | two-pass loop | `Stats.variance` |
| median | `qsort` | `sort_by(total_cmp)` | `statistics.median` | `Float64Array.sort` | `Stats.median` |
| histogram | binary-search loop | `slice::partition_point` | `bisect.bisect_right` | binary-search loop | `Stats.histogram` |
| gcd | Euclid loop | Euclid loop | `math.gcd` | Euclid loop | `U32.gcd` |
| checked lcm | Euclid and U64 product | Euclid and `checked_mul` | `math.lcm` and U32 bound check | Euclid and division bound check | `U32.lcm` |
| isqrt | integer binary search | `u32::isqrt` | `math.isqrt` | integer binary search | `U32.isqrt` |

C and JavaScript have no statistics in the standard library, and Rust's has none either, so those use the obvious loop. Python's `statistics.variance` rounds the exact value once, and Python's `sum` compensates. Both give a variance that differs from the plain two-pass loop in the low bits, so the Python program sums with a plain loop for that op. The sum of the values is exact here, so `fmean` matches the loop.

Bend uses the soft-float in `bend-kit-f64`. The other languages use a hardware double. The C program copies the words with `memcpy`, so it assumes a little-endian host.

## Results

M4 Pro, macOS, 2026-11-13. Bend 2.0.38, Apple clang 21.0.0 (`-O2`), rustc 1.91.0, Bun 1.4.4, Node 24.0.1, Python 3.14.6. Median of three runs. Times are in ms.

| op | C | Rust | Bun | Node | Python | Bend |
|---|---:|---:|---:|---:|---:|---:|
| mean | 0.005 | 0.006 | 0.608 | 0.476 | 0.027 | 0.287 |
| variance | 0.012 | 0.011 | 0.546 | 0.616 | 0.264 | 0.875 |
| median | 0.576 | 0.129 | 0.097 | 0.483 | 0.684 | 3.818 |

The checksums are `3422847917` for the mean, `1370401302` for the variance, and `1092607460` for the median, in every program.

Bend's mean and variance are about 50 to 80 times slower than C. That is the soft-float add and multiply, about 30 ns each. The median sorts a linked list with `List.sort` and soft-float compares, about 7 times slower than C's `qsort`. Bun and Node include JIT warm-up, because each op runs once.

## f64 0.1.3.0 re-pin

`python3 bench/run.py` from `stats/`, on the same machine and tool versions above, gives these medians of three runs. Times are in ms. All checksums remain the same in every language.

| op | C | Rust | Bun | Node | Python | Bend |
|---|---:|---:|---:|---:|---:|---:|
| mean | 0.005 | 0.006 | 0.586 | 0.455 | 0.029 | 0.286 |
| variance | 0.012 | 0.011 | 0.705 | 0.708 | 0.269 | 0.912 |
| median | 0.584 | 0.128 | 0.123 | 0.499 | 0.715 | 3.819 |

## Universal gcd symmetry

The same `python3 bench/run.py` command after argument ordering gives 0.314 ms for mean, 0.928 ms for variance, and 4.034 ms for median (three-run medians). All six languages retain the checksums above. These float operations do not call gcd.

## Histogram binary search

The histogram has 100 bins and 101 edges, `i * 10486` for `i = 0..100`. It uses the same 10000 draws as the other operations. The last bin is closed. Its checksum is the double word-xor of `sum((i + 1) * count[i])`, so bin placement, not only the total, affects it.

`python3 bench/run.py` from `stats/` on the machine and tool versions above gives these three-run medians in ms. Edge and count allocation are timed in every language.

| implementation | C | Rust | Bun | Node | Python | Bend |
|---|---:|---:|---:|---:|---:|---:|
| Before: one scan per bin | 0.187 | 0.045 | 1.109 | 0.924 | 1.173 | 10.042 |
| After: binary search | 0.098 | 0.062 | 1.373 | 0.957 | 1.156 | 0.416 |

The other languages use binary search in both rows. Bend is about 24 times faster. Every language gives histogram checksum `1092535808` in both runs. The final run also gives Bend mean 0.451 ms, variance 1.545 ms, and median 5.984 ms, with the same checksums as above. Unchanged operations vary between runs.

## Adjacent-rank selection

Before the change, `python3 bench/run.py` gives these three-run medians in ms on the same machine and tool versions:

| implementation | C | Rust | Bun | Node | Python | Bend |
|---|---:|---:|---:|---:|---:|---:|
| Median: full list sort | 0.879 | 0.273 | 0.139 | 0.491 | 0.681 | 4.950 |
| Median: adjacent-rank selection | 0.799 | 0.172 | 0.116 | 0.494 | 0.715 | 1.158 |

A native profiling probe used the same list and clock. Three-run medians were 0.441 ms to build and count `List.sort.runs`, 4.610 ms to sort with direct unsigned word comparisons, and 5.186 ms for the old soft-float median. Direct word order is valid only for this nonnegative fixture. Both sorts gave median checksum `1092607460`. Building singleton runs is a small part of the cost. Removing soft-float comparison logic saved about 0.576 ms. Most time remained in merge passes and list traffic; this probe does not separate their allocation and traversal costs.

The first selection trial ran two independent searches for adjacent ranks and took 4.502 ms. The retained implementation finds both ranks in one search. It keeps the first value above each retained bucket, so it does not select the second rank from scratch. Partitions keep equal values in input order. A logarithmic partition budget falls back to a stable sort of the remaining bucket, so adversarial pivots cannot force quadratic work.

The final `python3 bench/run.py` run gives:

| op | C | Rust | Bun | Node | Python | Bend |
|---|---:|---:|---:|---:|---:|---:|
| mean | 0.007 | 0.008 | 0.685 | 0.500 | 0.029 | 0.276 |
| variance | 0.013 | 0.015 | 0.699 | 0.692 | 0.284 | 1.000 |
| median | 0.799 | 0.172 | 0.116 | 0.494 | 0.715 | 1.158 |
| histogram | 0.171 | 0.049 | 1.530 | 0.917 | 1.181 | 0.273 |

Every language retains the four checksums above. Median is about 4.3 times faster than the preceding full-sort run. Timing varies between runs; no Array-sort experiment was needed after selection improved the fixed workload.

## Universal integer laws

`python3 bench/run.py 1` on 2026-11-15 confirms all four checksums above in C, Rust, Bun, Node, Python, and Bend. This is one checksum run, not a new timing baseline. These float workloads do not call gcd, lcm, or integer square root; their universal proofs and existing fixtures cover the integer changes.

## Integer workloads

Each integer workload uses 2097207 pairs, generated before timing:

- Eight edge pairs: `(0, 0)`, `(0, 0xFFFFFFFF)`, `(0xFFFFFFFF, 0)`, `(0xFFFFFFFF, 0xFFFFFFFF)`, `(0xFFFFFFFF, 1)`, `(65535, 65536)`, `(65536, 65537)`, and `(12, 18)`.
- All 47 consecutive Fibonacci pairs that fit U32, from `(0, 1)` through `(1836311903, 2971215073)`.
- 2097152 pairs from xorshift32, starting at seed 44. For each pair, `a = xs(x)` and `b = xs(a)`; the next seed is `b`. These draws keep all 32 bits.

Gcd and lcm use both values. Isqrt uses the first value. The lcm cases include zero, equal maximum values, coprime values with a product that fits, and products that overflow. Each program sums the results modulo 2^32. A checked lcm result above `0xFFFFFFFF` is `None` and contributes `0x9E3779B9`, not zero. Python computes `math.lcm` first and checks that bound. JavaScript checks the bound before multiplication, so every retained product is exact.

C and JavaScript have no standard-library integer gcd or isqrt. They use Euclid's loop and an integer binary-search loop. Rust has no standard-library gcd or lcm, so it uses Euclid's loop and `checked_mul`; its isqrt uses the standard library. No extra dependency is needed.

The first probe uses the same 55 edge and Fibonacci pairs with only 16 random pairs. The harness checks its checksums across all six implementations. Each program accepts the random-pair count as its first argument. The full input is large enough for even Rust's isqrt to take several milliseconds. The float workloads are unchanged.

### Results

Command from the repository root: `python3 stats/bench/run.py` (three runs, median). The run used a process monitor that kills a Bend process above 8 GiB RSS. The small probe passed before the full input. No process reached that limit.

M4 Pro, macOS 25.6.0 arm64, 2026-11-15. Bend 2.0.38 (native), Apple clang 21.0.0 (`-O2`), rustc 1.91.0 (`-C opt-level=3`), Bun 1.4.4, Node 24.0.1, Python 3.14.6. Times are in ms. Input generation is not timed. Traversal, calls, and checksum accumulation are timed. JavaScript includes JIT warm-up. Bend uses a shared list; the final traversal also releases that list.

| op | C | Rust | Bun | Node | Python | Bend |
|---|---:|---:|---:|---:|---:|---:|
| mean | 0.006 | 0.005 | 0.626 | 0.510 | 0.028 | 0.258 |
| variance | 0.011 | 0.011 | 0.615 | 0.754 | 0.271 | 0.894 |
| median | 0.581 | 0.129 | 0.101 | 0.495 | 0.704 | 1.008 |
| histogram | 0.099 | 0.035 | 1.058 | 0.950 | 1.202 | 0.268 |
| gcd | 124.400 | 124.029 | 830.388 | 714.705 | 318.521 | 135.605 |
| lcm | 124.711 | 123.512 | 828.964 | 519.887 | 515.763 | 133.552 |
| isqrt | 32.043 | 5.599 | 264.228 | 191.325 | 234.334 | 16.898 |

All six implementations agree in every run:

| op | checksum |
|---|---:|
| mean | 3422847917 |
| variance | 1370401302 |
| median | 1092607460 |
| histogram | 1092535808 |
| gcd | 18047959 |
| lcm | 3181042401 |
| isqrt | 1421540955 |

Bend's gcd and lcm are within about 9% of C and Rust. Its isqrt is about 3.0 times slower than Rust's standard library, but faster than the C binary-search loop. [Issue #771](https://github.com/paymog/bend-kit/issues/771) tracks that measured isqrt gap. The checksums exposed no integer correctness failure.
