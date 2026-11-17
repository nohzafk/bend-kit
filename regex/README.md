# regex

Regular expressions in pure Bend, with matching in linear time. It uses RE2 syntax and a Pike VM (a Thompson NFA with capture slots). It does not backtrack, so a pattern cannot cause ReDoS.

```bend
import bend-kit-regex@0.8.0.0/regex.bend as Re

# Re.compile(pat) is Some{re}, or None for a syntax error.
# Re.find(re, s) gives the leftmost match: the span of group 0, then one entry per group.
Re.find(re, "xaabbby")         # re = "(a+)(b+)": Some{[Some{Span{1, 6}}, Some{Span{1, 3}}, Some{Span{3, 6}}]}
Re.is_match(re, "abc")         # Bool

# Over a UTF-8 Bytes buffer (bend-kit-bytes). Each hands the buffer back; spans are byte offsets.
Re.find.bytes(re, b)           # Bytes & Maybe<List<Maybe<Span>>>
Re.is_match.bytes(re, b)       # Bytes & Bool
```

This package imports `bend-kit-bytes@0.3.3.0` and `bend-kit-unicode@0.1.0.0`. Import those versions for the byte buffer and Unicode APIs.

With a `String`, positions count its code points, not octets. With `Bytes`, the matcher decodes UTF-8 as it goes and positions are byte offsets, as in RE2 and Go; an invalid byte matches as one U+FFFD. While no match is in progress, both paths skip chars that cannot start one, looking past leading assertions such as `\b` and `^`. The `Bytes` path is still the faster one. A group that did not take part in the match is `None`. The semantics are leftmost-first, as in RE2 and Perl: `a|ab` against `ab` matches `a`.

## Syntax

| | |
|---|---|
| Literals | `a`, `\.`, `\n \t \r \f \v` |
| Any char but `\n` | `.` |
| Classes | `[abc]`, `[a-z]`, `[^a-z]`, `[]a]`, `[a-]` |
| Perl classes (ASCII) | `\d \D \w \W \s \S`, also inside `[...]` |
| Unicode categories | `\pL`, `\p{Lu}`, `\PL`, `\P{Nd}`, also inside `[...]` |
| Alternation | `a\|b` |
| Repetition | `* + ? {n} {n,} {n,m}`, lazy with a trailing `?`; counts go up to 1000 |
| Groups | `(a)` captures, `(?:a)` does not |
| Anchors | `^ \A` start of text, `$ \z` end of text, `\b \B` word boundary |
| Case folding | a leading `(?i)`, for the whole pattern |

These are syntax errors, not silent mismatches: any flag but a leading `(?i)` (so `a(?i)b`, `(?i:a)` and `(?s)`), named groups, `\x` hex escapes, POSIX classes such as `[:alpha:]`, backreferences, and a repetition of a repetition (`a**`). The `LAWS.bend` fixtures, and 600 random patterns, give the same spans as Go's `regexp`, which implements RE2.

## Case folding

`(?i)` uses Unicode's simple case folding, as RE2 does: two code points match each other when `CaseFolding.txt` (statuses C and S) folds them to the same code point. So `(?i)k` matches `k`, `K` and the Kelvin sign U+212A, and `(?i)σ` matches `σ`, `ς` and `Σ`. There is no full folding: `(?i)ss` does not match `ß`. A class takes in every code point equivalent to one of its members, before `[^...]` negates it: `(?i)\w` and `(?i)[a-z]` match U+017F and U+212A, and `(?i)\W` and `(?i)\P{Lu}` match neither the folded nor the original members. `\d`, `\s`, `.` and `\b` are unchanged.

`fold.bend` holds the classes, generated from UCD 17.0 by `python3 regex/fold.py`. They equal Go's `unicode.SimpleFold` for every code point. A folded class reads the table only for a char that misses the class itself; a folded literal is a set of its equivalents, built when the pattern compiles.

## Cost

Matching takes O(n·m·log m) steps for n chars and m instructions. Each char advances every live thread once. The program and the set of visited states are binary tries keyed by pc, so each step costs O(log pc). `(a*)*b` against n a's, which a backtracker takes exponential time to reject, in a native build on an Apple M-series Mac:

| n | 25 000 | 50 000 | 100 000 | 200 000 |
|---|---|---|---|---|
| ms | 33 | 67 | 133 | 267 |

`is_match` on a program of at most 32 instructions with no `\b` or `\B` runs as a bit-parallel NFA instead: O(n·k) steps for k character sets. The table above times `find`.

Over `Bytes`, a program without `\b` or `\B` can run as a lazy DFA: each Pike VM step on an ASCII char is learned once per state, with the capture slots it saves, and replayed from a table after that. Non-ASCII chars, the last char, and states past the cache's size take the plain step. Short texts with large programs use the plain VM instead of learning states they rarely revisit. Other short texts use eight states; long texts use 256 for small programs or 2048 for large programs (a 2 MiB transition table). State keys use a hash-indexed trie with collision checks.

For a required ASCII byte, the `Bytes` matcher skips text without it. For a program of at most 32 reverse instructions with no assertions, a bitset DFA scans backward from each occurrence to find possible starts. A forward pass then preserves leftmost-first order and captures. If a reverse scan encounters non-ASCII bytes, exceeds 4096 bytes, or sees too many candidates, the normal matcher takes over.
