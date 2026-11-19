# Dependency plans with proved order and closure, incremental invalidation, and a build runner.
import Base
import bend-kit-bytes@0.3.3.0/bytes.bend as Bytes
import bend-kit-hash@0.3.0.4/hash.bend as Hash
import bend-kit-files@0.3.1.0/files.bend as Files
import bend-kit-process@0.5.0.1/process.bend as Proc

# A node and the nodes it requires. Its prerequisites must succeed before it runs.
type Node<-K: Data> is Data:
  Node{id: K, deps: List<&2, K>}

type Error<-K: Data> is Data:
  # node is undefined; chain is the requirement path from a target to the node that names it.
  Missing{node: K, chain: List<&2, K>}
  # Each node requires the next, and the last is the first.
  Cycle{path: List<&2, K>}
  # The candidate failed the plan check. This is a planner bug.
  Refused{}

type Status is Data:
  # The command ran and exited 0.
  Built{}
  # The node was not stale, so its command did not run.
  Fresh{}
  # The command ran and failed.
  Failed{}
  # The node is undefined, or a prerequisite did not succeed.
  Skipped{}

type Entry<-K: Data> is Data:
  Entry{node: K, status: Status}

type Action is Data:
  # Run the command, then record Built or Failed.
  Run{}
  # Record this status without a run.
  Mark{status: Status}
  # The node already has a status.
  Pass{}

def when(-A: Type, rest: Unit -> A, hit: Bool, yes: A) -> A:
  match hit:
    case True{}:
      yes
    case False{}:
      rest(Unit{})

# eq(k, x) for some x of xs.
def member(~K: Data, ~eq: K -> K -> Bool, xs: List<&2, K>, +k: K) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      when(Bool, u => member(~K, ~eq, t, k), eq(k, x), True{})

# Every x of xs is a member of ys.
def all_in(~K: Data, ~eq: K -> K -> Bool, xs: List<&2, K>, +ys: List<&2, K>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(member(~K, ~eq, ys, x), all_in(~K, ~eq, t, ys))

# Some x of xs is a member of ys.
def any_in(~K: Data, ~eq: K -> K -> Bool, xs: List<&2, K>, +ys: List<&2, K>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Bool.or(member(~K, ~eq, ys, x), any_in(~K, ~eq, t, ys))

# No element occurs twice.
def distinct(~K: Data, ~eq: K -> K -> Bool, xs: List<&2, K>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      Bool.and(Bool.not(member(~K, ~eq, t, x)), distinct(~K, ~eq, t))

def rev(-K: Data, xs: List<&2, K>, acc: List<&2, K>) -> List<&2, K>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      rev(K, t, x <> acc)

def cat(-K: Data, xs: List<&2, K>, ys: List<&2, K>) -> List<&2, K>:
  match xs:
    case Nil{}:
      ys
    case Con{x, t}:
      x <> cat(K, t, ys)

# The prerequisites of the first node named k; None when no node is.
def deps(~K: Data, ~eq: K -> K -> Bool, g: List<&2, Node<K>>, +k: K) -> Maybe<&2, List<&2, K>>:
  match g:
    case Nil{}:
      None{}
    case Con{Node{+id, +ds}, t}:
      when(Maybe<&2, List<&2, K>>, u => deps(~K, ~eq, t, k), eq(k, id), Some{ds})

def deps.or_nil(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, Node<K>>, +k: K) -> List<&2, K>:
  Maybe.default(&2, List<&2, K>, deps(~K, ~eq, g, k), Nil{})

# Plan check
# ----------

def ordered.node(~K: Data, ~eq: K -> K -> Bool, m: Maybe<&2, List<&2, K>>, +done: List<&2, K>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{ds}:
      all_in(~K, ~eq, ds, done)

# Each node is defined, is not in done, and has every prerequisite in done; it then joins done.
def ordered(~K: Data, ~eq: K -> K -> Bool, p: List<&2, K>, +g: List<&2, Node<K>>, +done: List<&2, K>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Bool.not(member(~K, ~eq, done, x)),
        Bool.and(ordered.node(~K, ~eq, deps(~K, ~eq, g, x), done),
          ordered(~K, ~eq, t, g, x <> done)))

# Over the plan reversed: each node is in want, a target or a prerequisite of a later node.
def needed(~K: Data, ~eq: K -> K -> Bool, r: List<&2, K>, +g: List<&2, Node<K>>, +want: List<&2, K>) -> Bool:
  match r:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(member(~K, ~eq, want, x), needed(~K, ~eq, t, g, cat(K, deps.or_nil(~K, ~eq, g, x), want)))

# p is a dependency order of exactly the closure of ts.
def valid(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, Node<K>>, +ts: List<&2, K>, +p: List<&2, K>) -> Bool:
  Bool.and(ordered(~K, ~eq, p, g, Nil{}),
    Bool.and(needed(~K, ~eq, rev(K, p, Nil{}), g, ts), all_in(~K, ~eq, ts, p)))

# Planning
# --------

type Frame<-K: Data> is Data:
  Visit{node: K}
  Leave{node: K}

# Each arm is a closure, so only the taken one runs.
def branch(-A: Type, c: Bool, yes: Unit -> A, no: Unit -> A) -> A:
  match c:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def maybe.case(-A: Data, -R: Type, m: Maybe<&2, A>, none: Unit -> R, some: A -> R) -> R:
  match m:
    case None{}:
      none(Unit{})
    case Some{x}:
      some(x)

def enters(-K: Data, xs: List<&2, K>, rest: List<&2, Frame<K>>) -> List<&2, Frame<K>>:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Visit{x} <> enters(K, t, rest)

# The open path up to and including k, nearest first.
def upto(~K: Data, ~eq: K -> K -> Bool, path: List<&2, K>, +k: K) -> List<&2, K>:
  match path:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      when(List<&2, K>, u => x <> upto(~K, ~eq, t, k), eq(k, x), [x])

def cycle(~K: Data, ~eq: K -> K -> Bool, path: List<&2, K>, +k: K) -> Error<K>:
  Cycle{cat(K, rev(K, upto(~K, ~eq, path, k), Nil{}), [k])}

# One step per frame. path holds the open nodes, nearest first; out the finished ones, last first.
def visit(
  ~K: Data, ~eq: K -> K -> Bool, fuel: Nat, +g: List<&2, Node<K>>,
  stack: List<&2, Frame<K>>, +path: List<&2, K>, +out: List<&2, K>
) -> Result<&2, &2, Error<K>, List<&2, K>>:
  match fuel:
    case 0n:
      Fail{Refused{}}
    case 1n+(+f):
      match stack:
        case Nil{}:
          Done{out}
        case Con{Leave{k}, rest}:
          visit(~K, ~eq, f, g, rest, List.tail(&2, K, path), k <> out)
        case Con{Visit{+k}, +rest}:
          branch(Result<&2, &2, Error<K>, List<&2, K>>, member(~K, ~eq, out, k),
            u => visit(~K, ~eq, f, g, rest, path, out),
            u => branch(Result<&2, &2, Error<K>, List<&2, K>>, member(~K, ~eq, path, k),
              u => Fail{cycle(~K, ~eq, path, k)},
              u => maybe.case(List<&2, K>, Result<&2, &2, Error<K>, List<&2, K>>, deps(~K, ~eq, g, k),
                u => Fail{Missing{k, rev(K, path, Nil{})}},
                ds => visit(~K, ~eq, f, g, enters(K, ds, Leave{k} <> rest), k <> path, out))))

# Enough steps: one per target, and one per node and per edge, plus the final one.
def fuel(-K: Data, g: List<&2, Node<K>>, n: Nat) -> Nat:
  match g:
    case Nil{}:
      1n+n
    case Con{Node{id, ds}, t}:
      fuel(K, t, Nat.add(1n+List.length(&2, K, ds), n))

def plan.ok(-K: Data, c: Bool, p: List<&2, K>) -> Result<&2, &2, Error<K>, List<&2, K>>:
  match c:
    case True{}:
      Done{p}
    case False{}:
      Fail{Refused{}}

def plan.check(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, Node<K>>, +ts: List<&2, K>, r: Result<&2, &2, Error<K>, List<&2, K>>) -> Result<&2, &2, Error<K>, List<&2, K>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{out}:
      +p = rev(K, out, Nil{})
      plan.ok(K, valid(~K, ~eq, g, ts, p), p)

# The closure of ts in dependency order, each node once; or why there is none.
def plan(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, Node<K>>, +ts: List<&2, K>) -> Result<&2, &2, Error<K>, List<&2, K>>:
  plan.check(~K, ~eq, g, ts,
    visit(~K, ~eq, fuel(K, g, List.length(&2, K, ts)), g, enters(K, ts, Nil{}), Nil{}, Nil{}))

# Invalidation
# ------------

def invalidate.if(-K: Data, hit: Bool, x: K, acc: List<&2, K>) -> List<&2, K>:
  match hit:
    case True{}:
      x <> acc
    case False{}:
      acc

def invalidate.go(~K: Data, ~eq: K -> K -> Bool, p: List<&2, K>, +g: List<&2, Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>) -> List<&2, K>:
  match p:
    case Nil{}:
      acc
    case Con{+x, t}:
      invalidate.go(~K, ~eq, t, g, changed,
        invalidate.if(K, Bool.or(member(~K, ~eq, changed, x), any_in(~K, ~eq, deps.or_nil(~K, ~eq, g, x), acc)), x, acc))

# The nodes of p that changed or require a stale node, latest first.
def invalidate(~K: Data, ~eq: K -> K -> Bool, p: List<&2, K>, +g: List<&2, Node<K>>, +changed: List<&2, K>) -> List<&2, K>:
  invalidate.go(~K, ~eq, p, g, changed, Nil{})

# Execution
# ---------

def status(~K: Data, ~eq: K -> K -> Bool, st: List<&2, Entry<K>>, +k: K) -> Maybe<&2, Status>:
  match st:
    case Nil{}:
      None{}
    case Con{Entry{+x, +s}, t}:
      when(Maybe<&2, Status>, u => status(~K, ~eq, t, k), eq(k, x), Some{s})

def Status.ok(s: Status) -> Bool:
  match s:
    case Built{}:
      True{}
    case Fresh{}:
      True{}
    case Failed{}:
      False{}
    case Skipped{}:
      False{}

# Built, Fresh, or Failed: the node was not skipped.
def Status.selected(s: Status) -> Bool:
  match s:
    case Skipped{}:
      False{}
    case _:
      True{}

def ok.at(m: Maybe<&2, Status>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Status.ok(s)

def selected.at(m: Maybe<&2, Status>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Status.selected(s)

# Every node of ds is Built or Fresh in st.
def ready(~K: Data, ~eq: K -> K -> Bool, ds: List<&2, K>, +st: List<&2, Entry<K>>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, t}:
      Bool.and(ok.at(status(~K, ~eq, st, d)), ready(~K, ~eq, t, st))

def decide.ready(go: Bool, stale: Bool) -> Action:
  match go:
    case False{}:
      Mark{Skipped{}}
    case True{}:
      match stale:
        case True{}:
          Run{}
        case False{}:
          Mark{Fresh{}}

def decide.node(~K: Data, ~eq: K -> K -> Bool, m: Maybe<&2, List<&2, K>>, stale: Bool, +st: List<&2, Entry<K>>) -> Action:
  match m:
    case None{}:
      Mark{Skipped{}}
    case Some{ds}:
      decide.ready(ready(~K, ~eq, ds, st), stale)

def decide.seen(~K: Data, ~eq: K -> K -> Bool, seen: Bool, +g: List<&2, Node<K>>, +stale: List<&2, K>, +st: List<&2, Entry<K>>, +x: K) -> Action:
  match seen:
    case True{}:
      Pass{}
    case False{}:
      decide.node(~K, ~eq, deps(~K, ~eq, g, x), member(~K, ~eq, stale, x), st)

# What to do with x: run it, mark it without a run, or pass it.
def decide(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, Node<K>>, +stale: List<&2, K>, +st: List<&2, Entry<K>>, +x: K) -> Action:
  decide.seen(~K, ~eq, Maybe.is_some(&2, Status, status(~K, ~eq, st, x)), g, stale, st, x)

def outcome(rs: List<&2, Bool>) -> Status:
  match rs:
    case Con{True{}, t}:
      Built{}
    case _:
      Failed{}

# The status that action a records; a Run takes its result from the head of rs.
def Action.status(a: Action, rs: List<&2, Bool>) -> Maybe<&2, Status>:
  match a:
    case Run{}:
      Some{outcome(rs)}
    case Mark{s}:
      Some{s}
    case Pass{}:
      None{}

def record(-K: Data, m: Maybe<&2, Status>, st: List<&2, Entry<K>>, x: K) -> List<&2, Entry<K>>:
  match m:
    case None{}:
      st
    case Some{s}:
      Entry{x, s} <> st

def step(-K: Data, a: Action, st: List<&2, Entry<K>>, x: K, rs: List<&2, Bool>) -> List<&2, Entry<K>>:
  record(K, Action.status(a, rs), st, x)

def step.rest(a: Action, rs: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Run{}:
      List.tail(&2, Bool, rs)
    case _:
      rs

# The model of a run: rs holds the result of each command, in order. Statuses are newest first.
def exec(
  ~K: Data, ~eq: K -> K -> Bool, p: List<&2, K>, +g: List<&2, Node<K>>, +stale: List<&2, K>,
  +st: List<&2, Entry<K>>, +rs: List<&2, Bool>
) -> List<&2, Entry<K>>:
  match p:
    case Nil{}:
      st
    case Con{+x, t}:
      +a = decide(~K, ~eq, g, stale, st, x)
      exec(~K, ~eq, t, g, stale, step(K, a, st, x, rs), step.rest(a, rs))

def keys(-K: Data, st: List<&2, Entry<K>>) -> List<&2, K>:
  match st:
    case Nil{}:
      Nil{}
    case Con{Entry{x, s}, t}:
      x <> keys(K, t)

# Builds
# ------

# A node with its command and the source files it reads.
type Task is Data:
  # argv is the command and its arguments; an empty argv is a group with no command.
  Task{id: String, deps: List<&2, String>, argv: List<&2, String>, inputs: List<&2, String>}

def Run(-A: Type) -> Type:
  IO(Result<&1, &1, U32 & String, A>)

def Run.pure(-A: Type, x: A) -> Run(A):
  IO.pure(Result<&1, &1, U32 & String, A>, Done{x})

def Run.fail(-A: Type, e: U32 & String) -> Run(A):
  IO.pure(Result<&1, &1, U32 & String, A>, Fail{e})

def Run.next(-A: Type, -B: Type, r: Result<&1, &1, U32 & String, A>, f: A -> Run(B)) -> Run(B):
  match r:
    case Done{x}:
      f(x)
    case Fail{e}:
      Run.fail(B, e)

def Run.bind(-A: Type, -B: Type, m: Run(A), f: A -> Run(B)) -> Run(B):
  IO.bind(Result<&1, &1, U32 & String, A>, Result<&1, &1, U32 & String, B>, m, r => Run.next(A, B, r, f))

def Run.lift(-A: Type, m: IO(A)) -> Run(A):
  IO.bind(A, Result<&1, &1, U32 & String, A>, m, x => Run.pure(A, x))

def Task.node(t: Task) -> Node<String>:
  match t:
    case Task{id, ds, a, i}:
      Node{id, ds}

def graph(ts: List<&2, Task>) -> List<&2, Node<String>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      Task.node(t) <> graph(r)

# The first task named k.
def task(ts: List<&2, Task>, +k: String) -> Maybe<&2, Task>:
  match ts:
    case Nil{}:
      None{}
    case Con{Task{+id, +ds, +a, +i}, r}:
      when(Maybe<&2, Task>, u => task(r, k), String.eq(k, id), Some{Task{id, ds, a, i}})

def id.char(c: Char) -> Bool:
  +n = Char.to_u32(c)
  Bool.and((n >= 32 : U32), (n <= 126 : U32))

def id.chars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(id.char(c), id.chars(t))

# A stamp file holds one id per line, so an id is printable ASCII and not empty.
def id.ok(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), id.chars(s))

def ids.bad(ts: List<&2, Task>) -> Maybe<&2, String>:
  match ts:
    case Nil{}:
      None{}
    case Con{Task{+id, ds, a, i}, r}:
      when(Maybe<&2, String>, u => ids.bad(r), Bool.not(id.ok(id)), Some{id})

def Error.show(e: Error<String>) -> String:
  match e:
    case Missing{n, Nil{}}:
      "missing node " ++ n
    case Missing{n, chain}:
      "missing node " ++ n ++ ", required by " ++ String.join(chain, " -> ")
    case Cycle{path}:
      "cycle: " ++ String.join(path, " -> ")
    case Refused{}:
      "the plan check refused the candidate; this is a planner bug"

def Status.show(s: Status) -> String:
  match s:
    case Built{}:
      "built"
    case Fresh{}:
      "fresh"
    case Failed{}:
      "failed"
    case Skipped{}:
      "skipped"

# Each code point in decimal, so distinct strings give distinct text.
def text(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{c, t}:
      U32.show(Char.to_u32(c)) ++ "," ++ text(t)

def texts(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      text(x) ++ ";" ++ texts(t)

def digest.of(r: Bytes.Bytes & Hash.W64) -> String:
  match r:
    case (b, Hash.W64{hi, lo}):
      U32.show(hi) ++ "." ++ U32.show(lo)

def digest(b: Bytes.Bytes) -> String:
  digest.of(Hash.xxh64(b, Hash.W64{0, 0}))

def file.end(empty: Bool, f: File, acc: Bytes.Bytes, b: Bytes.Bytes, k: File -> Bytes.Bytes -> IO(Bytes.Bytes)) -> IO(Bytes.Bytes):
  match empty:
    case True{}:
      do IO<Bytes.Bytes>:
        File.close(f)
        return acc
    case False{}:
      k(f)(Bytes.append(acc, b))

def file.got(r: File & Result<&1, &1, U32 & String, Bytes.Bytes>, acc: Bytes.Bytes, k: File -> Bytes.Bytes -> IO(Bytes.Bytes)) -> IO(Bytes.Bytes):
  match r:
    case (f, Fail{e}):
      do IO<Bytes.Bytes>:
        File.close(f)
        return Bytes.append(acc, Bytes.from_string("unreadable"))
    case (f, Done{b}):
      Bytes.Bytes{+len, buf} = b
      file.end(U32.is_eq(len, 0), f, acc, Bytes.Bytes{len, buf}, k)

# The rest of f, read 1 MiB at a time, in at most n reads.
def file.more(n: Nat, f: File, acc: Bytes.Bytes) -> IO(Bytes.Bytes):
  match n:
    case 0n:
      do IO<Bytes.Bytes>:
        File.close(f)
        return acc
    case 1n+m:
      IO.bind(File & Result<&1, &1, U32 & String, Bytes.Bytes>, Bytes.Bytes, Files.read_bytes(f, 1048576),
        r => file.got(r, acc, g => b => file.more(m, g, b)))

def file.opened(r: Result<&1, &1, U32 & String, File>) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "m")
    case Done{f}:
      IO.bind(Bytes.Bytes, String, file.more(4097n, f, Bytes.new(0)), b => IO.pure(String, "f" ++ digest(b)))

# "m" when path does not open, else "f" and the hash of its octets.
def file.stamp(path: String) -> IO(String):
  IO.bind(Result<&1, &1, U32 & String, File>, String, File.open(path, "r"), r => file.opened(r))

def inputs.stamp(xs: List<&2, String>, +dir: String, acc: String) -> IO(String):
  match xs:
    case Nil{}:
      IO.pure(String, acc)
    case Con{+x, t}:
      IO.bind(String, String, file.stamp(Files.path.join(dir, x)), s => inputs.stamp(t, dir, acc ++ text(x) ++ ":" ++ s ++ ";"))

# The hash of the command, the prerequisites, and every input file.
def Task.stamp(t: Task, +dir: String) -> IO(String):
  match t:
    case Task{id, ds, a, ins}:
      IO.bind(String, String, inputs.stamp(ins, dir, "argv:" ++ texts(a) ++ "deps:" ++ texts(ds) ++ "inputs:"),
        s => IO.pure(String, digest(Bytes.from_string(s))))

# A node and the hash of its command, prerequisites, and inputs.
type Stamp is Data:
  Stamp{node: String, hash: String}

def lookup(xs: List<&2, Stamp>, +k: String) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case Con{Stamp{+x, +v}, t}:
      when(Maybe<&2, String>, u => lookup(t, k), String.eq(k, x), Some{v})

def stamps.now(p: List<&2, String>, +ts: List<&2, Task>, +dir: String, acc: List<&2, Stamp>) -> IO(List<&2, Stamp>):
  match p:
    case Nil{}:
      IO.pure(List<&2, Stamp>, acc)
    case Con{+x, t}:
      IO.bind(String, List<&2, Stamp>,
        Task.stamp(Maybe.default(&2, Task, task(ts, x), Task{x, Nil{}, Nil{}, Nil{}}), dir),
        s => stamps.now(t, ts, dir, Stamp{x, s} <> acc))

def same(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      String.eq(x, y)
    case _ _:
      False{}

# The nodes of p whose stamp now is not the recorded one.
def changed(p: List<&2, String>, +old: List<&2, Stamp>, +now: List<&2, Stamp>) -> List<&2, String>:
  match p:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      invalidate.if(String, Bool.not(same(lookup(old, x), lookup(now, x))), x, changed(t, old, now))

# The stamps of the nodes that ended Built or Fresh, and the old stamps of nodes the run did not reach.
def after.new(st: List<&2, Entry<String>>, +now: List<&2, Stamp>) -> List<&2, Stamp>:
  match st:
    case Nil{}:
      Nil{}
    case Con{Entry{+x, s}, t}:
      +r = after.new(t, now)
      Bool.pick(List<&2, Stamp>, Status.ok(s), Stamp{x, Maybe.default(&2, String, lookup(now, x), "")} <> r, r)

def after.keep(old: List<&2, Stamp>, +done: List<&2, String>) -> List<&2, Stamp>:
  match old:
    case Nil{}:
      Nil{}
    case Con{Stamp{+k, +v}, t}:
      +r = after.keep(t, done)
      Bool.pick(List<&2, Stamp>, member(~String, ~String.eq, done, k), r, Stamp{k, v} <> r)

def after(+st: List<&2, Entry<String>>, +now: List<&2, Stamp>, old: List<&2, Stamp>) -> List<&2, Stamp>:
  cat(Stamp, after.new(st, now), after.keep(old, keys(String, st)))

def stamps.line(e: Stamp) -> String:
  match e:
    case Stamp{k, v}:
      v ++ "\t" ++ k ++ "\n"

def stamps.lines(xs: List<&2, Stamp>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{e, t}:
      stamps.line(e) ++ stamps.lines(t)

def stamps.show(xs: List<&2, Stamp>) -> String:
  stamps.lines(xs)

def stamps.entry(fields: List<&2, String>) -> List<&2, Stamp>:
  match fields:
    case Con{v, Con{k, Nil{}}}:
      [Stamp{k, v}]
    case _:
      Nil{}

def stamps.parse(lines: List<&2, String>) -> List<&2, Stamp>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      cat(Stamp, stamps.entry(String.split(l, '\t')), stamps.parse(t))

def stamps.got(r: File & Result<&1, &1, U32 & String, String>) -> IO(List<&2, Stamp>):
  match r:
    case (f, Fail{e}):
      do IO<List<&2, Stamp>>:
        File.close(f)
        return Nil{}
    case (f, Done{s}):
      do IO<List<&2, Stamp>>:
        File.close(f)
        return stamps.parse(String.lines(s))

def stamps.opened(r: Result<&1, &1, U32 & String, File>) -> IO(List<&2, Stamp>):
  match r:
    case Fail{e}:
      IO.pure(List<&2, Stamp>, Nil{})
    case Done{f}:
      IO.bind(File & Result<&1, &1, U32 & String, String>, List<&2, Stamp>, File.read(f, 268435456), q => stamps.got(q))

# The recorded stamps; none when the file does not open.
def stamps.read(path: String) -> IO(List<&2, Stamp>):
  IO.bind(Result<&1, &1, U32 & String, File>, List<&2, Stamp>, File.open(path, "r"), r => stamps.opened(r))

def stamps.closed(r: File & Result<&1, &1, U32 & String, Unit>) -> Run(Unit):
  match r:
    case (f, x):
      do IO<Result<&1, &1, U32 & String, Unit>>:
        File.close(f)
        return x

# Writes through path.tmp and a rename, so a reader sees the old file or the new one.
def stamps.write(+path: String, xs: List<&2, Stamp>) -> Run(Unit):
  +tmp = path ++ ".tmp"
  do Run<Unit>:
    f : File <- File.open(tmp, "w")
    r : File & Result<&1, &1, U32 & String, Unit> <- Run.lift(File & Result<&1, &1, U32 & String, Unit>, File.write(f, stamps.show(xs)))
    stamps.closed(r)
    Files.rename(tmp, path)

# What a command left: its exit code and the last 4096 octets of its stdout and stderr, or why it did not start.
type Ran is Data:
  Exited{code: U32, out: String, err: String}
  Unstarted{error: String}

type Log is Data:
  Log{node: String, ran: Ran}

# A planned node, its status, and what its command left; None when no command ran.
type Outcome is Data:
  Outcome{node: String, status: Status, ran: Maybe<&2, Ran>}

type Ledger is Data:
  Ledger{st: List<&2, Entry<String>>, logs: List<&2, Log>}

def Ran.ok(r: Ran) -> Bool:
  match r:
    case Exited{code, o, e}:
      U32.is_eq(code, 0)
    case Unstarted{e}:
      False{}

def tail.of(r: Bytes.Bytes & Bytes.Bytes) -> String:
  match r:
    case (b, t):
      Bytes.to_string(t)

# The last 4096 octets of b, one Char per octet.
def tail(b: Bytes.Bytes) -> String:
  Bytes.Bytes{+len, buf} = b
  +n = U32.min(len, 4096)
  tail.of(Bytes.slice(Bytes.Bytes{len, buf}, (len - n : U32), n))

def run.ran(r: Result<&1, &1, U32 & String, U32 & Bytes.Bytes & Bytes.Bytes>) -> Ran:
  match r:
    case Fail{(code, msg)}:
      Unstarted{msg}
    case Done{(code, (out, err))}:
      Exited{code, tail(out), tail(err)}

# Runs argv in dir; None for a group with no command.
def run.argv(argv: List<&2, String>, dir: String) -> IO(Maybe<&2, Ran>):
  match argv:
    case Nil{}:
      IO.pure(Maybe<&2, Ran>, None{})
    case Con{cmd, args}:
      IO.bind(Result<&1, &1, U32 & String, U32 & Bytes.Bytes & Bytes.Bytes>, Maybe<&2, Ran>, Proc.run(cmd, args, Nil{}, dir, Bytes.new(0)),
        r => IO.pure(Maybe<&2, Ran>, Some{run.ran(r)}))

def run.task(dir: String, m: Maybe<&2, Task>) -> IO(Maybe<&2, Ran>):
  match m:
    case None{}:
      IO.pure(Maybe<&2, Ran>, Some{Unstarted{"undefined task"}})
    case Some{Task{id, ds, argv, ins}}:
      run.argv(argv, dir)

# A group succeeds; a command succeeds when it exits 0.
def run.ok(m: Maybe<&2, Ran>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{r}:
      Ran.ok(r)

def run.log(+x: String, m: Maybe<&2, Ran>, logs: List<&2, Log>) -> List<&2, Log>:
  match m:
    case None{}:
      logs
    case Some{r}:
      Log{x, r} <> logs

def act(-R: Type, a: Action, run: Unit -> R, other: Unit -> R) -> R:
  match a:
    case Run{}:
      run(Unit{})
    case _:
      other(Unit{})

# exec, with each Run's result from the task's command.
def run.loop(
  p: List<&2, String>, +ts: List<&2, Task>, +g: List<&2, Node<String>>, +stale: List<&2, String>,
  +st: List<&2, Entry<String>>, +logs: List<&2, Log>, +dir: String
) -> IO(Ledger):
  match p:
    case Nil{}:
      IO.pure(Ledger, Ledger{st, logs})
    case Con{+x, +t}:
      +a = decide(~String, ~String.eq, g, stale, st, x)
      act(IO(Ledger), a,
        u => IO.bind(Maybe<&2, Ran>, Ledger, run.task(dir, task(ts, x)),
          +m => run.loop(t, ts, g, stale, step(String, Run{}, st, x, [run.ok(m)]), run.log(x, m, logs), dir)),
        u => run.loop(t, ts, g, stale, step(String, a, st, x, Nil{}), logs, dir))

def ran.find(logs: List<&2, Log>, +k: String) -> Maybe<&2, Ran>:
  match logs:
    case Nil{}:
      None{}
    case Con{Log{+x, +r}, t}:
      when(Maybe<&2, Ran>, u => ran.find(t, k), String.eq(k, x), Some{r})

def outcomes(st: List<&2, Entry<String>>, +logs: List<&2, Log>, acc: List<&2, Outcome>) -> List<&2, Outcome>:
  match st:
    case Nil{}:
      acc
    case Con{Entry{+x, s}, t}:
      outcomes(t, logs, Outcome{x, s, ran.find(logs, x)} <> acc)

def build.ids(m: Maybe<&2, String>) -> Run(Unit):
  match m:
    case None{}:
      Run.pure(Unit, Unit{})
    case Some{id}:
      Run.fail(Unit, (22, "task id is empty or not printable ASCII: " ++ text(id)))

def build.plan(r: Result<&2, &2, Error<String>, List<&2, String>>) -> Run(List<&2, String>):
  match r:
    case Fail{e}:
      Run.fail(List<&2, String>, (22, Error.show(e)))
    case Done{p}:
      Run.pure(List<&2, String>, p)

def build.done(+path: String, +now: List<&2, Stamp>, old: List<&2, Stamp>, l: Ledger) -> Run(List<&2, Outcome>):
  match l:
    case Ledger{+st, logs}:
      do Run<List<&2, Outcome>>:
        stamps.write(path, after(st, now, old))
        return outcomes(st, logs, Nil{})

# Plans targets, runs each stale task in dir, reuses the rest, and records stamps in path.
# The result is each planned node with its status and command output, in plan order.
def build(+tasks: List<&2, Task>, +targets: List<&2, String>, +dir: String, +path: String) -> Run(List<&2, Outcome>):
  +g = graph(tasks)
  do Run<List<&2, Outcome>>:
    build.ids(ids.bad(tasks))
    +p : List<&2, String> <- build.plan(plan(~String, ~String.eq, g, targets))
    +old : List<&2, Stamp> <- Run.lift(List<&2, Stamp>, stamps.read(path))
    +now : List<&2, Stamp> <- Run.lift(List<&2, Stamp>, stamps.now(p, tasks, dir, Nil{}))
    +stale : List<&2, String> = invalidate(~String, ~String.eq, p, g, changed(p, old, now))
    l : Ledger <- Run.lift(Ledger, run.loop(p, tasks, g, stale, Nil{}, Nil{}, dir))
    build.done(path, now, old, l)
