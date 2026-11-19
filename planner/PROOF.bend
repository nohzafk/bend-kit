import Base
import ./planner.bend as P
import ./LAWS.bend as Laws

# Bool
# ----

def true_ne_false(e: {True{} == False{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Unit, Empty)
  Unit{}

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))

def and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(h))

def not_true(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_ne_true(h))
    case False{}:
      {==}

def or_false_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, true_ne_false(h))
    case False{}:
      h

def none_ne_some(-T: Data, -x: T, e: {None{} == Some{x} : Maybe<&2, T>}) -> Empty:
  %e : Bool.pick(Type, Maybe.is_some(&2, T, _), Empty, Unit)
  Unit{}

def some_inj(-T: Data, +a: T, -b: T, e: {Some{a} == Some{b} : Maybe<&2, T>}) -> {a == b : T}:
  Equal.cong(Maybe<&2, T>, T, m => Maybe.default(&2, T, m, a), Some{a}, Some{b}, e)

def fail_ne_done(-E: Data, -A: Data, -e: E, -x: A, h: {Fail{e} == Done{x} : Result<&2, &2, E, A>}) -> Empty:
  %h : Bool.pick(Type, Result.is_done(&2, &2, E, A, _), Empty, Unit)
  Unit{}

def done_inj(-E: Data, -A: Data, +a: A, -b: A, h: {Done{a} == Done{b} : Result<&2, &2, E, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, E, A>, A, r => Result.default(&2, &2, E, A, r, a), Done{a}, Done{b}, h)

# Membership
# ----------

def Sound(~K: Data, ~eq: K -> K -> Bool) -> Type:
  @x: K -> @y: K -> {eq(x, y) == True{} : Bool} -> {x == y : K}

def mem_hit(~K: Data, ~eq: K -> K -> Bool, +x: K, +t: List<&2, K>, +k: K, e: {eq(k, x) == True{} : Bool}) ->
  {P.member(~K, ~eq, x <> t, k) == True{} : Bool}:
  %Equal.sym(Bool, eq(k, x), True{}, e) : {P.when(Bool, u => P.member(~K, ~eq, t, k), _, True{}) == True{} : Bool}
  {==}

def mem_miss(~K: Data, ~eq: K -> K -> Bool, +x: K, +t: List<&2, K>, +k: K, e: {eq(k, x) == False{} : Bool}) ->
  {P.member(~K, ~eq, x <> t, k) == P.member(~K, ~eq, t, k) : Bool}:
  %Equal.sym(Bool, eq(k, x), False{}, e) : {P.when(Bool, u => P.member(~K, ~eq, t, k), _, True{}) == P.member(~K, ~eq, t, k) : Bool}
  {==}

def all_in_mem.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +x: K, +t: List<&2, K>, +ys: List<&2, K>, +d: K,
  hc: {eq(d, x) == c : Bool}, hx: {P.member(~K, ~eq, ys, x) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, d) == True{} : Bool} -> {P.member(~K, ~eq, ys, d) == True{} : Bool},
  hm: {P.member(~K, ~eq, x <> t, d) == True{} : Bool}
) -> {P.member(~K, ~eq, ys, d) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(K, d, x, sound(d, x, hc)) : {P.member(~K, ~eq, ys, _) == True{} : Bool}
      hx
    case False{}:
      ih(Equal.trans(Bool, P.member(~K, ~eq, t, d), P.member(~K, ~eq, x <> t, d), True{},
        Equal.sym(Bool, P.member(~K, ~eq, x <> t, d), P.member(~K, ~eq, t, d), mem_miss(~K, ~eq, x, t, d, hc)), hm))

# A member of xs is a member of ys when all_in(xs, ys).
def all_in_mem(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), xs: List<&2, K>, +ys: List<&2, K>, +d: K,
  ha: {P.all_in(~K, ~eq, xs, ys) == True{} : Bool}, hm: {P.member(~K, ~eq, xs, d) == True{} : Bool}
) -> {P.member(~K, ~eq, ys, d) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, ys, d) == True{} : Bool}, false_ne_true(hm))
    case Con{+x, +t}:
      +ha = ha
      all_in_mem.if(~K, ~eq, ~sound, eq(d, x), x, t, ys, d, {==},
        and_l(P.member(~K, ~eq, ys, x), P.all_in(~K, ~eq, t, ys), ha),
        h => all_in_mem(~K, ~eq, ~sound, t, ys, d, and_r(P.member(~K, ~eq, ys, x), P.all_in(~K, ~eq, t, ys), ha), h),
        hm)

# The plan check
# --------------

def plan_valid.ok(
  ~K: Data, ~eq: K -> K -> Bool, c: Bool, +g: List<&2, P.Node<K>>, +ts: List<&2, K>, +q: List<&2, K>, -p: List<&2, K>,
  hc: {P.valid(~K, ~eq, g, ts, q) == c : Bool},
  h: {P.plan.ok(K, c, q) == Done{p} : Result<&2, &2, P.Error<K>, List<&2, K>>}
) -> {P.valid(~K, ~eq, g, ts, p) == True{} : Bool}:
  match c:
    case True{}:
      %done_inj(P.Error<K>, List<&2, K>, q, p, h) : {P.valid(~K, ~eq, g, ts, _) == True{} : Bool}
      hc
    case False{}:
      Empty.absurd({P.valid(~K, ~eq, g, ts, p) == True{} : Bool}, fail_ne_done(P.Error<K>, List<&2, K>, P.Refused{}, p, h))

# A plan passed the check.
def plan_valid(
  ~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +ts: List<&2, K>, r: Result<&2, &2, P.Error<K>, List<&2, K>>, -p: List<&2, K>,
  h: {P.plan.check(~K, ~eq, g, ts, r) == Done{p} : Result<&2, &2, P.Error<K>, List<&2, K>>}
) -> {P.valid(~K, ~eq, g, ts, p) == True{} : Bool}:
  match r:
    case Fail{e}:
      Empty.absurd({P.valid(~K, ~eq, g, ts, p) == True{} : Bool}, fail_ne_done(P.Error<K>, List<&2, K>, e, p, h))
    case Done{out}:
      +q = P.rev(K, out, Nil{})
      plan_valid.ok(~K, ~eq, P.valid(~K, ~eq, g, ts, q), g, ts, q, p, {==}, h)

def plan_ordered(
  ~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +ts: List<&2, K>, +p: List<&2, K>,
  h: {P.plan(~K, ~eq, g, ts) == Done{p} : Result<&2, &2, P.Error<K>, List<&2, K>>}
) -> {P.ordered(~K, ~eq, p, g, Nil{}) == True{} : Bool}:
  and_l(P.ordered(~K, ~eq, p, g, Nil{}), Bool.and(P.needed(~K, ~eq, P.rev(K, p, Nil{}), g, ts), P.all_in(~K, ~eq, ts, p)),
    plan_valid(~K, ~eq, g, ts, P.visit(~K, ~eq, P.fuel(K, g, List.length(&2, K, ts)), g, P.enters(K, ts, Nil{}), Nil{}, Nil{}), p, h))

def plan_needed(
  ~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +ts: List<&2, K>, +p: List<&2, K>,
  h: {P.plan(~K, ~eq, g, ts) == Done{p} : Result<&2, &2, P.Error<K>, List<&2, K>>}
) -> {P.needed(~K, ~eq, P.rev(K, p, Nil{}), g, ts) == True{} : Bool}:
  and_l(P.needed(~K, ~eq, P.rev(K, p, Nil{}), g, ts), P.all_in(~K, ~eq, ts, p),
    and_r(P.ordered(~K, ~eq, p, g, Nil{}), Bool.and(P.needed(~K, ~eq, P.rev(K, p, Nil{}), g, ts), P.all_in(~K, ~eq, ts, p)),
      plan_valid(~K, ~eq, g, ts, P.visit(~K, ~eq, P.fuel(K, g, List.length(&2, K, ts)), g, P.enters(K, ts, Nil{}), Nil{}, Nil{}), p, h)))

def plan_covers(
  ~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +ts: List<&2, K>, +p: List<&2, K>,
  h: {P.plan(~K, ~eq, g, ts) == Done{p} : Result<&2, &2, P.Error<K>, List<&2, K>>}
) -> {P.all_in(~K, ~eq, ts, p) == True{} : Bool}:
  and_r(P.needed(~K, ~eq, P.rev(K, p, Nil{}), g, ts), P.all_in(~K, ~eq, ts, p),
    and_r(P.ordered(~K, ~eq, p, g, Nil{}), Bool.and(P.needed(~K, ~eq, P.rev(K, p, Nil{}), g, ts), P.all_in(~K, ~eq, ts, p)),
      plan_valid(~K, ~eq, g, ts, P.visit(~K, ~eq, P.fuel(K, g, List.length(&2, K, ts)), g, P.enters(K, ts, Nil{}), Nil{}, Nil{}), p, h)))

def Laws.plan_targets(K, eq, sound, g, ts, p, t, h, ht):
  +g = g
  +ts = ts
  +p = p
  all_in_mem(~K, ~eq, ~sound, ts, p, t, plan_covers(~K, ~eq, g, ts, p, h), ht)

# More membership
# ---------------

def mem_cons_r.if(
  ~K: Data, ~eq: K -> K -> Bool, c: Bool, +x: K, +t: List<&2, K>, +k: K,
  hc: {eq(k, x) == c : Bool}, h: {P.member(~K, ~eq, t, k) == True{} : Bool}
) -> {P.member(~K, ~eq, x <> t, k) == True{} : Bool}:
  match c:
    case True{}:
      mem_hit(~K, ~eq, x, t, k, hc)
    case False{}:
      Equal.trans(Bool, P.member(~K, ~eq, x <> t, k), P.member(~K, ~eq, t, k), True{}, mem_miss(~K, ~eq, x, t, k, hc), h)

def mem_cons_r(
  ~K: Data, ~eq: K -> K -> Bool, +x: K, +t: List<&2, K>, +k: K, h: {P.member(~K, ~eq, t, k) == True{} : Bool}
) -> {P.member(~K, ~eq, x <> t, k) == True{} : Bool}:
  mem_cons_r.if(~K, ~eq, eq(k, x), x, t, k, {==}, h)

# The tail of a match that misses its head.
def mem_tail(
  ~K: Data, ~eq: K -> K -> Bool, +x: K, +t: List<&2, K>, +k: K,
  hc: {eq(k, x) == False{} : Bool}, h: {P.member(~K, ~eq, x <> t, k) == True{} : Bool}
) -> {P.member(~K, ~eq, t, k) == True{} : Bool}:
  Equal.trans(Bool, P.member(~K, ~eq, t, k), P.member(~K, ~eq, x <> t, k), True{},
    Equal.sym(Bool, P.member(~K, ~eq, x <> t, k), P.member(~K, ~eq, t, k), mem_miss(~K, ~eq, x, t, k, hc)), h)

def mem_tail_false(
  ~K: Data, ~eq: K -> K -> Bool, +x: K, +t: List<&2, K>, +k: K,
  hc: {eq(k, x) == False{} : Bool}, h: {P.member(~K, ~eq, x <> t, k) == False{} : Bool}
) -> {P.member(~K, ~eq, t, k) == False{} : Bool}:
  Equal.trans(Bool, P.member(~K, ~eq, t, k), P.member(~K, ~eq, x <> t, k), False{},
    Equal.sym(Bool, P.member(~K, ~eq, x <> t, k), P.member(~K, ~eq, t, k), mem_miss(~K, ~eq, x, t, k, hc)), h)

def mem_cons_false(
  ~K: Data, ~eq: K -> K -> Bool, +x: K, +t: List<&2, K>, +k: K,
  hc: {eq(k, x) == False{} : Bool}, h: {P.member(~K, ~eq, t, k) == False{} : Bool}
) -> {P.member(~K, ~eq, x <> t, k) == False{} : Bool}:
  Equal.trans(Bool, P.member(~K, ~eq, x <> t, k), P.member(~K, ~eq, t, k), False{}, mem_miss(~K, ~eq, x, t, k, hc), h)

def clash(-b: Bool, ht: {b == True{} : Bool}, hf: {b == False{} : Bool}) -> Empty:
  true_ne_false(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, ht), hf))

def or_false_l(a: Bool, -b: Bool, hz: {a == False{} : Bool}, h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, true_ne_false(hz))
    case False{}:
      h

def and_not_false(a: Bool, -b: Bool, ha: {a == False{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(Bool.not(a), b) == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.and(Bool.not(True{}), b) == True{} : Bool}, true_ne_false(ha))
    case False{}:
      hb

def and_true(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, false_ne_true(ha))

def rev_mem_r(
  ~K: Data, ~eq: K -> K -> Bool, xs: List<&2, K>, +acc: List<&2, K>, +k: K, h: {P.member(~K, ~eq, acc, k) == True{} : Bool}
) -> {P.member(~K, ~eq, P.rev(K, xs, acc), k) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+x, t}:
      rev_mem_r(~K, ~eq, t, x <> acc, k, mem_cons_r(~K, ~eq, x, acc, k, h))

def rev_mem_l.if(
  ~K: Data, ~eq: K -> K -> Bool, c: Bool, +x: K, +t: List<&2, K>, +acc: List<&2, K>, +k: K,
  hc: {eq(k, x) == c : Bool}, h: {P.member(~K, ~eq, x <> t, k) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, k) == True{} : Bool} -> {P.member(~K, ~eq, P.rev(K, t, x <> acc), k) == True{} : Bool}
) -> {P.member(~K, ~eq, P.rev(K, t, x <> acc), k) == True{} : Bool}:
  match c:
    case True{}:
      rev_mem_r(~K, ~eq, t, x <> acc, k, mem_hit(~K, ~eq, x, acc, k, hc))
    case False{}:
      ih(mem_tail(~K, ~eq, x, t, k, hc, h))

def rev_mem_l(
  ~K: Data, ~eq: K -> K -> Bool, xs: List<&2, K>, +acc: List<&2, K>, +k: K, h: {P.member(~K, ~eq, xs, k) == True{} : Bool}
) -> {P.member(~K, ~eq, P.rev(K, xs, acc), k) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, acc, k) == True{} : Bool}, false_ne_true(h))
    case Con{+x, +t}:
      rev_mem_l.if(~K, ~eq, eq(k, x), x, t, acc, k, {==}, h, hm => rev_mem_l(~K, ~eq, t, x <> acc, k, hm))

def rev_mem_inv.if(
  ~K: Data, ~eq: K -> K -> Bool, c: Bool, +x: K, +t: List<&2, K>, +acc: List<&2, K>, +k: K,
  hc: {eq(k, x) == c : Bool}, hn: {P.member(~K, ~eq, acc, k) == False{} : Bool},
  ih: {P.member(~K, ~eq, x <> acc, k) == False{} : Bool} -> {P.member(~K, ~eq, t, k) == True{} : Bool}
) -> {P.member(~K, ~eq, x <> t, k) == True{} : Bool}:
  match c:
    case True{}:
      mem_hit(~K, ~eq, x, t, k, hc)
    case False{}:
      mem_cons_r(~K, ~eq, x, t, k, ih(mem_cons_false(~K, ~eq, x, acc, k, hc, hn)))

# A member of rev(xs, acc) that is not in acc is in xs.
def rev_mem_inv(
  ~K: Data, ~eq: K -> K -> Bool, xs: List<&2, K>, +acc: List<&2, K>, +k: K,
  h: {P.member(~K, ~eq, P.rev(K, xs, acc), k) == True{} : Bool}, hn: {P.member(~K, ~eq, acc, k) == False{} : Bool}
) -> {P.member(~K, ~eq, xs, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, Nil{}, k) == True{} : Bool}, clash(P.member(~K, ~eq, acc, k), h, hn))
    case Con{+x, +t}:
      rev_mem_inv.if(~K, ~eq, eq(k, x), x, t, acc, k, {==}, hn, hm => rev_mem_inv(~K, ~eq, t, x <> acc, k, h, hm))

def rev_not.if(
  ~K: Data, ~eq: K -> K -> Bool, c: Bool, xs: List<&2, K>, +acc: List<&2, K>, +k: K,
  hc: {P.member(~K, ~eq, xs, k) == c : Bool}, h: {P.member(~K, ~eq, P.rev(K, xs, acc), k) == False{} : Bool}
) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, clash(P.member(~K, ~eq, P.rev(K, xs, acc), k), rev_mem_l(~K, ~eq, xs, acc, k, hc), h))
    case False{}:
      {==}

def rev_not(
  ~K: Data, ~eq: K -> K -> Bool, +xs: List<&2, K>, +acc: List<&2, K>, +k: K,
  h: {P.member(~K, ~eq, P.rev(K, xs, acc), k) == False{} : Bool}
) -> {P.member(~K, ~eq, xs, k) == False{} : Bool}:
  rev_not.if(~K, ~eq, P.member(~K, ~eq, xs, k), xs, acc, k, {==}, h)

# Order
# -----

def ord_cat(
  ~K: Data, ~eq: K -> K -> Bool, pre: List<&2, K>, +rest: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>,
  h: {P.ordered(~K, ~eq, P.cat(K, pre, rest), g, done) == True{} : Bool}
) -> {P.ordered(~K, ~eq, rest, g, P.rev(K, pre, done)) == True{} : Bool}:
  match pre:
    case Nil{}:
      h
    case Con{+y, +t}:
      ord_cat(~K, ~eq, t, rest, g, y <> done,
        and_r(P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done), P.ordered(~K, ~eq, P.cat(K, t, rest), g, y <> done),
          and_r(Bool.not(P.member(~K, ~eq, done, y)),
            Bool.and(P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done), P.ordered(~K, ~eq, P.cat(K, t, rest), g, y <> done)), h)))

# The facts that ordered checks for the head y.
def ord_fresh(
  ~K: Data, ~eq: K -> K -> Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>,
  h: {P.ordered(~K, ~eq, y <> t, g, done) == True{} : Bool}
) -> {P.member(~K, ~eq, done, y) == False{} : Bool}:
  not_true(P.member(~K, ~eq, done, y), and_l(Bool.not(P.member(~K, ~eq, done, y)),
    Bool.and(P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done), P.ordered(~K, ~eq, t, g, y <> done)), h))

def ord_node(
  ~K: Data, ~eq: K -> K -> Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>,
  h: {P.ordered(~K, ~eq, y <> t, g, done) == True{} : Bool}
) -> {P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done) == True{} : Bool}:
  and_l(P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done), P.ordered(~K, ~eq, t, g, y <> done),
    and_r(Bool.not(P.member(~K, ~eq, done, y)),
      Bool.and(P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done), P.ordered(~K, ~eq, t, g, y <> done)), h))

def ord_rest(
  ~K: Data, ~eq: K -> K -> Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>,
  h: {P.ordered(~K, ~eq, y <> t, g, done) == True{} : Bool}
) -> {P.ordered(~K, ~eq, t, g, y <> done) == True{} : Bool}:
  and_r(P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done), P.ordered(~K, ~eq, t, g, y <> done),
    and_r(Bool.not(P.member(~K, ~eq, done, y)),
      Bool.and(P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done), P.ordered(~K, ~eq, t, g, y <> done)), h))

def node_some(~K: Data, ~eq: K -> K -> Bool, m: Maybe<&2, List<&2, K>>, +done: List<&2, K>,
  h: {P.ordered.node(~K, ~eq, m, done) == True{} : Bool}
) -> {Maybe.is_some(&2, List<&2, K>, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))
    case Some{ds}:
      {==}

# ordered.node at a node whose prerequisites are ds: all of ds are done.
def node_all(
  ~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +x: K, +ds: List<&2, K>, +done: List<&2, K>,
  hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>},
  h: {P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, x), done) == True{} : Bool}
) -> {P.all_in(~K, ~eq, ds, done) == True{} : Bool}:
  Equal.trans(Bool, P.all_in(~K, ~eq, ds, done), P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, x), done), True{},
    Equal.sym(Bool, P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, x), done), P.all_in(~K, ~eq, ds, done),
      Equal.cong(Maybe<&2, List<&2, K>>, Bool, m => P.ordered.node(~K, ~eq, m, done), P.deps(~K, ~eq, g, x), Some{ds}, hd)), h)

# ordered.node moved along x == y.
def node_move(
  ~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +x: K, +y: K, +done: List<&2, K>,
  e: {x == y : K}, h: {P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done) == True{} : Bool}
) -> {P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, x), done) == True{} : Bool}:
  Equal.trans(Bool, P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, x), done), P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done), True{},
    Equal.cong(K, Bool, z => P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, z), done), x, y, e), h)

def defined_go.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>, +x: K,
  hc: {eq(x, y) == c : Bool}, hO: {P.ordered(~K, ~eq, y <> t, g, done) == True{} : Bool},
  hx: {P.member(~K, ~eq, y <> t, x) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, x) == True{} : Bool} -> {Maybe.is_some(&2, List<&2, K>, P.deps(~K, ~eq, g, x)) == True{} : Bool}
) -> {Maybe.is_some(&2, List<&2, K>, P.deps(~K, ~eq, g, x)) == True{} : Bool}:
  match c:
    case True{}:
      node_some(~K, ~eq, P.deps(~K, ~eq, g, x), done, node_move(~K, ~eq, g, x, y, done, sound(x, y, hc), ord_node(~K, ~eq, y, t, g, done, hO)))
    case False{}:
      ih(mem_tail(~K, ~eq, y, t, x, hc, hx))

def defined_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>, +x: K,
  hO: {P.ordered(~K, ~eq, p, g, done) == True{} : Bool}, hx: {P.member(~K, ~eq, p, x) == True{} : Bool}
) -> {Maybe.is_some(&2, List<&2, K>, P.deps(~K, ~eq, g, x)) == True{} : Bool}:
  match p:
    case Nil{}:
      Empty.absurd({Maybe.is_some(&2, List<&2, K>, P.deps(~K, ~eq, g, x)) == True{} : Bool}, false_ne_true(hx))
    case Con{+y, +t}:
      +hO = hO
      defined_go.if(~K, ~eq, ~sound, eq(x, y), y, t, g, done, x, {==}, hO, hx,
        hm => defined_go(~K, ~eq, ~sound, t, g, y <> done, x, ord_rest(~K, ~eq, y, t, g, done, hO), hm))

def Laws.plan_defined(K, eq, sound, g, ts, p, x, h, hx):
  +g = g
  +ts = ts
  +p = p
  defined_go(~K, ~eq, ~sound, p, g, Nil{}, x, plan_ordered(~K, ~eq, g, ts, p, h), hx)

def split_ordered(
  ~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +ts: List<&2, K>, +pre: List<&2, K>, +x: K, +post: List<&2, K>,
  h: {P.plan(~K, ~eq, g, ts) == Done{P.cat(K, pre, x <> post)} : Result<&2, &2, P.Error<K>, List<&2, K>>}
) -> {P.ordered(~K, ~eq, x <> post, g, P.rev(K, pre, Nil{})) == True{} : Bool}:
  ord_cat(~K, ~eq, pre, x <> post, g, Nil{}, plan_ordered(~K, ~eq, g, ts, P.cat(K, pre, x <> post), h))

def Laws.plan_before(K, eq, sound, g, ts, pre, x, post, ds, d, h, hd, hm):
  +g = g
  +pre = pre
  +x = x
  +post = post
  +ds = ds
  +d = d
  +done = P.rev(K, pre, Nil{})
  rev_mem_inv(~K, ~eq, pre, Nil{}, d,
    all_in_mem(~K, ~eq, ~sound, ds, done, d,
      node_all(~K, ~eq, g, x, ds, done, hd, ord_node(~K, ~eq, x, post, g, done, split_ordered(~K, ~eq, g, ts, pre, x, post, h))),
      hm),
    {==})

def Laws.plan_once(K, eq, sound, g, ts, pre, x, post, h):
  +g = g
  +pre = pre
  +x = x
  +post = post
  +done = P.rev(K, pre, Nil{})
  rev_not(~K, ~eq, pre, Nil{}, x, ord_fresh(~K, ~eq, x, post, g, done, split_ordered(~K, ~eq, g, ts, pre, x, post, h)))

def closed_go.d(
  ~K: Data, ~eq: K -> K -> Bool, c: Bool, +y: K, +t: List<&2, K>, +done: List<&2, K>, +d: K,
  hc: {eq(d, y) == c : Bool}, hnd: {P.member(~K, ~eq, done, d) == False{} : Bool},
  ih: {P.member(~K, ~eq, y <> done, d) == False{} : Bool} -> {P.member(~K, ~eq, t, d) == True{} : Bool}
) -> {P.member(~K, ~eq, y <> t, d) == True{} : Bool}:
  match c:
    case True{}:
      mem_hit(~K, ~eq, y, t, d, hc)
    case False{}:
      mem_cons_r(~K, ~eq, y, t, d, ih(mem_cons_false(~K, ~eq, y, done, d, hc, hnd)))

def closed_go.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>,
  +x: K, +ds: List<&2, K>, +d: K,
  hc: {eq(x, y) == c : Bool}, hO: {P.ordered(~K, ~eq, y <> t, g, done) == True{} : Bool}, hx: {P.member(~K, ~eq, y <> t, x) == True{} : Bool},
  hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>}, hm: {P.member(~K, ~eq, ds, d) == True{} : Bool},
  hnd: {P.member(~K, ~eq, done, d) == False{} : Bool},
  ih: {P.member(~K, ~eq, t, x) == True{} : Bool} -> {P.member(~K, ~eq, y <> done, d) == False{} : Bool} -> {P.member(~K, ~eq, t, d) == True{} : Bool}
) -> {P.member(~K, ~eq, y <> t, d) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({P.member(~K, ~eq, y <> t, d) == True{} : Bool},
        clash(P.member(~K, ~eq, done, d),
          all_in_mem(~K, ~eq, ~sound, ds, done, d,
            node_all(~K, ~eq, g, x, ds, done, hd, node_move(~K, ~eq, g, x, y, done, sound(x, y, hc), ord_node(~K, ~eq, y, t, g, done, hO))), hm),
          hnd))
    case False{}:
      closed_go.d(~K, ~eq, eq(d, y), y, t, done, d, {==}, hnd, ih(mem_tail(~K, ~eq, y, t, x, hc, hx)))

# A prerequisite of a node of p that is not done is in p.
def closed_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>,
  +x: K, +ds: List<&2, K>, +d: K,
  hO: {P.ordered(~K, ~eq, p, g, done) == True{} : Bool}, hx: {P.member(~K, ~eq, p, x) == True{} : Bool},
  hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>}, hm: {P.member(~K, ~eq, ds, d) == True{} : Bool},
  hnd: {P.member(~K, ~eq, done, d) == False{} : Bool}
) -> {P.member(~K, ~eq, p, d) == True{} : Bool}:
  match p:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, Nil{}, d) == True{} : Bool}, false_ne_true(hx))
    case Con{+y, +t}:
      +hO = hO
      +hd = hd
      +hm = hm
      closed_go.if(~K, ~eq, ~sound, eq(x, y), y, t, g, done, x, ds, d, {==}, hO, hx, hd, hm, hnd,
        h1 => h2 => closed_go(~K, ~eq, ~sound, t, g, y <> done, x, ds, d, ord_rest(~K, ~eq, y, t, g, done, hO), h1, hd, hm, h2))

def Laws.plan_closed(K, eq, sound, g, ts, p, x, ds, d, h, hx, hd, hm):
  +g = g
  +ts = ts
  +p = p
  closed_go(~K, ~eq, ~sound, p, g, Nil{}, x, ds, d, plan_ordered(~K, ~eq, g, ts, p, h), hx, hd, hm, {==})

# Least
# -----

def all_in_cat(
  ~K: Data, ~eq: K -> K -> Bool, a: List<&2, K>, +b: List<&2, K>, +s: List<&2, K>,
  ha: {P.all_in(~K, ~eq, a, s) == True{} : Bool}, hb: {P.all_in(~K, ~eq, b, s) == True{} : Bool}
) -> {P.all_in(~K, ~eq, P.cat(K, a, b), s) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+x, +t}:
      +ha = ha
      and_true(P.member(~K, ~eq, s, x), P.all_in(~K, ~eq, P.cat(K, t, b), s),
        and_l(P.member(~K, ~eq, s, x), P.all_in(~K, ~eq, t, s), ha),
        all_in_cat(~K, ~eq, t, b, s, and_r(P.member(~K, ~eq, s, x), P.all_in(~K, ~eq, t, s), ha), hb))

def closed_mem.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +z: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +s: List<&2, K>, +y: K,
  hc: {eq(y, z) == c : Bool}, hz: {P.all_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, z), s) == True{} : Bool},
  hy: {P.member(~K, ~eq, z <> t, y) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, y) == True{} : Bool} -> {P.all_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), s) == True{} : Bool}
) -> {P.all_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), s) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(K, y, z, sound(y, z, hc)) : {P.all_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, _), s) == True{} : Bool}
      hz
    case False{}:
      ih(mem_tail(~K, ~eq, z, t, y, hc, hy))

def closed_mem(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), xs: List<&2, K>, +g: List<&2, P.Node<K>>, +s: List<&2, K>, +y: K,
  hc: {Laws.closed(~K, ~eq, xs, g, s) == True{} : Bool}, hy: {P.member(~K, ~eq, xs, y) == True{} : Bool}
) -> {P.all_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), s) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({P.all_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), s) == True{} : Bool}, false_ne_true(hy))
    case Con{+z, +t}:
      +hc = hc
      closed_mem.if(~K, ~eq, ~sound, eq(y, z), z, t, g, s, y, {==},
        and_l(P.all_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, z), s), Laws.closed(~K, ~eq, t, g, s), hc), hy,
        hm => closed_mem(~K, ~eq, ~sound, t, g, s, y, and_r(P.all_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, z), s), Laws.closed(~K, ~eq, t, g, s), hc), hm))

def needed_sub.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +y: K, +t: List<&2, K>, +s: List<&2, K>, +x: K,
  hc: {eq(x, y) == c : Bool}, hy: {P.member(~K, ~eq, s, y) == True{} : Bool}, hx: {P.member(~K, ~eq, y <> t, x) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, x) == True{} : Bool} -> {P.member(~K, ~eq, s, x) == True{} : Bool}
) -> {P.member(~K, ~eq, s, x) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(K, x, y, sound(x, y, hc)) : {P.member(~K, ~eq, s, _) == True{} : Bool}
      hy
    case False{}:
      ih(mem_tail(~K, ~eq, y, t, x, hc, hx))

# Every node that needed walks is in a closed set that holds want.
def needed_sub(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), r: List<&2, K>, +g: List<&2, P.Node<K>>, +want: List<&2, K>, +s: List<&2, K>, +x: K,
  hN: {P.needed(~K, ~eq, r, g, want) == True{} : Bool}, hw: {P.all_in(~K, ~eq, want, s) == True{} : Bool},
  hcl: {Laws.closed(~K, ~eq, s, g, s) == True{} : Bool}, hx: {P.member(~K, ~eq, r, x) == True{} : Bool}
) -> {P.member(~K, ~eq, s, x) == True{} : Bool}:
  match r:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, s, x) == True{} : Bool}, false_ne_true(hx))
    case Con{+y, +t}:
      +hN = hN
      +hw = hw
      +hcl = hcl
      +dn = P.deps.or_nil(~K, ~eq, g, y)
      +hy = all_in_mem(~K, ~eq, ~sound, want, s, y, hw, and_l(P.member(~K, ~eq, want, y), P.needed(~K, ~eq, t, g, P.cat(K, dn, want)), hN))
      needed_sub.if(~K, ~eq, ~sound, eq(x, y), y, t, s, x, {==}, hy, hx,
        hm => needed_sub(~K, ~eq, ~sound, t, g, P.cat(K, dn, want), s, x,
          and_r(P.member(~K, ~eq, want, y), P.needed(~K, ~eq, t, g, P.cat(K, dn, want)), hN),
          all_in_cat(~K, ~eq, dn, want, s, closed_mem(~K, ~eq, ~sound, s, g, s, y, hcl, hy), hw),
          hcl, hm))

def Laws.plan_least(K, eq, sound, g, ts, s, hts, hcl, p, x, h, hx):
  +g = g
  +ts = ts
  +p = p
  +x = x
  needed_sub(~K, ~eq, ~sound, P.rev(K, p, Nil{}), g, ts, s, x, plan_needed(~K, ~eq, g, ts, p, h), hts, hcl,
    rev_mem_l(~K, ~eq, p, Nil{}, x, hx))

# Cycles
# ------

# No member of done is in c.
def disj(~K: Data, ~eq: K -> K -> Bool, done: List<&2, K>, +c: List<&2, K>) -> Bool:
  match done:
    case Nil{}:
      True{}
    case Con{+z, t}:
      Bool.and(Bool.not(P.member(~K, ~eq, c, z)), disj(~K, ~eq, t, c))

def disj_mem.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +z: K, +t: List<&2, K>, +c: List<&2, K>, +w: K,
  hb: {eq(w, z) == b : Bool}, hz: {P.member(~K, ~eq, c, z) == False{} : Bool}, hw: {P.member(~K, ~eq, z <> t, w) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, w) == True{} : Bool} -> {P.member(~K, ~eq, c, w) == False{} : Bool}
) -> {P.member(~K, ~eq, c, w) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(K, w, z, sound(w, z, hb)) : {P.member(~K, ~eq, c, _) == False{} : Bool}
      hz
    case False{}:
      ih(mem_tail(~K, ~eq, z, t, w, hb, hw))

def disj_mem(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), done: List<&2, K>, +c: List<&2, K>, +w: K,
  hd: {disj(~K, ~eq, done, c) == True{} : Bool}, hw: {P.member(~K, ~eq, done, w) == True{} : Bool}
) -> {P.member(~K, ~eq, c, w) == False{} : Bool}:
  match done:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, c, w) == False{} : Bool}, false_ne_true(hw))
    case Con{+z, +t}:
      +hd = hd
      disj_mem.if(~K, ~eq, ~sound, eq(w, z), z, t, c, w, {==},
        not_true(P.member(~K, ~eq, c, z), and_l(Bool.not(P.member(~K, ~eq, c, z)), disj(~K, ~eq, t, c), hd)), hw,
        hm => disj_mem(~K, ~eq, ~sound, t, c, w, and_r(Bool.not(P.member(~K, ~eq, c, z)), disj(~K, ~eq, t, c), hd), hm))

def cyclic_mem.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +z: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +c: List<&2, K>, +y: K,
  hb: {eq(y, z) == b : Bool}, hz: {P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, z), c) == True{} : Bool},
  hy: {P.member(~K, ~eq, z <> t, y) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, y) == True{} : Bool} -> {P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), c) == True{} : Bool}
) -> {P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), c) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(K, y, z, sound(y, z, hb)) : {P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, _), c) == True{} : Bool}
      hz
    case False{}:
      ih(mem_tail(~K, ~eq, z, t, y, hb, hy))

def cyclic_mem(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), xs: List<&2, K>, +g: List<&2, P.Node<K>>, +c: List<&2, K>, +y: K,
  hc: {Laws.cyclic(~K, ~eq, xs, g, c) == True{} : Bool}, hy: {P.member(~K, ~eq, xs, y) == True{} : Bool}
) -> {P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), c) == True{} : Bool}, false_ne_true(hy))
    case Con{+z, +t}:
      +hc = hc
      cyclic_mem.if(~K, ~eq, ~sound, eq(y, z), z, t, g, c, y, {==},
        and_l(P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, z), c), Laws.cyclic(~K, ~eq, t, g, c), hc), hy,
        hm => cyclic_mem(~K, ~eq, ~sound, t, g, c, y, and_r(P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, z), c), Laws.cyclic(~K, ~eq, t, g, c), hc), hm))

def any_all_disj.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +w: K, +t: List<&2, K>, +done: List<&2, K>, +c: List<&2, K>,
  hb: {P.member(~K, ~eq, c, w) == b : Bool}, hw: {P.member(~K, ~eq, done, w) == True{} : Bool},
  hd: {disj(~K, ~eq, done, c) == True{} : Bool}, hy: {Bool.or(b, P.any_in(~K, ~eq, t, c)) == True{} : Bool},
  ih: {P.any_in(~K, ~eq, t, c) == True{} : Bool} -> Empty
) -> Empty:
  match b:
    case True{}:
      clash(P.member(~K, ~eq, c, w), hb, disj_mem(~K, ~eq, ~sound, done, c, w, hd, hw))
    case False{}:
      ih(hy)

# No prerequisite list lies wholly in done and meets c, when done misses c.
def any_all_disj(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), ds: List<&2, K>, +done: List<&2, K>, +c: List<&2, K>,
  ha: {P.all_in(~K, ~eq, ds, done) == True{} : Bool}, hy: {P.any_in(~K, ~eq, ds, c) == True{} : Bool},
  hd: {disj(~K, ~eq, done, c) == True{} : Bool}
) -> Empty:
  match ds:
    case Nil{}:
      false_ne_true(hy)
    case Con{+w, +t}:
      +ha = ha
      +hd = hd
      any_all_disj.if(~K, ~eq, ~sound, P.member(~K, ~eq, c, w), w, t, done, c, {==},
        and_l(P.member(~K, ~eq, done, w), P.all_in(~K, ~eq, t, done), ha), hd, hy,
        h => any_all_disj(~K, ~eq, ~sound, t, done, c, and_r(P.member(~K, ~eq, done, w), P.all_in(~K, ~eq, t, done), ha), h, hd))

def cycle_head.m(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), m: Maybe<&2, List<&2, K>>, +done: List<&2, K>, +c: List<&2, K>,
  hn: {P.ordered.node(~K, ~eq, m, done) == True{} : Bool},
  hy: {P.any_in(~K, ~eq, Maybe.default(&2, List<&2, K>, m, Nil{}), c) == True{} : Bool},
  hd: {disj(~K, ~eq, done, c) == True{} : Bool}
) -> Empty:
  match m:
    case None{}:
      false_ne_true(hn)
    case Some{ds}:
      any_all_disj(~K, ~eq, ~sound, ds, done, c, hn, hy, hd)

def cycle_head.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +y: K, +g: List<&2, P.Node<K>>, +done: List<&2, K>, +c: List<&2, K>,
  hb: {P.member(~K, ~eq, c, y) == b : Bool}, hcy: {Laws.cyclic(~K, ~eq, c, g, c) == True{} : Bool},
  hn: {P.ordered.node(~K, ~eq, P.deps(~K, ~eq, g, y), done) == True{} : Bool}, hd: {disj(~K, ~eq, done, c) == True{} : Bool}
) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        cycle_head.m(~K, ~eq, ~sound, P.deps(~K, ~eq, g, y), done, c, hn, cyclic_mem(~K, ~eq, ~sound, c, g, c, y, hcy, hb), hd))
    case False{}:
      {==}

def cycle_go.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +y: K, +t: List<&2, K>, +c: List<&2, K>, +x: K,
  hb: {eq(x, y) == b : Bool}, hy: {P.member(~K, ~eq, c, y) == False{} : Bool}, hx: {P.member(~K, ~eq, y <> t, x) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, x) == True{} : Bool} -> {P.member(~K, ~eq, c, x) == False{} : Bool}
) -> {P.member(~K, ~eq, c, x) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(K, x, y, sound(x, y, hb)) : {P.member(~K, ~eq, c, _) == False{} : Bool}
      hy
    case False{}:
      ih(mem_tail(~K, ~eq, y, t, x, hb, hx))

def cycle_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>, +c: List<&2, K>, +x: K,
  hO: {P.ordered(~K, ~eq, p, g, done) == True{} : Bool}, hd: {disj(~K, ~eq, done, c) == True{} : Bool},
  hcy: {Laws.cyclic(~K, ~eq, c, g, c) == True{} : Bool}, hx: {P.member(~K, ~eq, p, x) == True{} : Bool}
) -> {P.member(~K, ~eq, c, x) == False{} : Bool}:
  match p:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, c, x) == False{} : Bool}, false_ne_true(hx))
    case Con{+y, +t}:
      +hO = hO
      +hd = hd
      +hcy = hcy
      +hy = cycle_head.if(~K, ~eq, ~sound, P.member(~K, ~eq, c, y), y, g, done, c, {==}, hcy, ord_node(~K, ~eq, y, t, g, done, hO), hd)
      cycle_go.if(~K, ~eq, ~sound, eq(x, y), y, t, c, x, {==}, hy, hx,
        hm => cycle_go(~K, ~eq, ~sound, t, g, y <> done, c, x, ord_rest(~K, ~eq, y, t, g, done, hO),
          and_not_false(P.member(~K, ~eq, c, y), disj(~K, ~eq, done, c), hy, hd), hcy, hm))

def Laws.plan_cycle(K, eq, sound, g, c, hc, ts, p, x, h, hx):
  +g = g
  +ts = ts
  +p = p
  cycle_go(~K, ~eq, ~sound, p, g, Nil{}, c, x, plan_ordered(~K, ~eq, g, ts, p, h), {==}, hc, hx)

def Laws.plan_cycle_target(K, eq, sound, g, c, hc, ts, t, ht, hct, p, h):
  +g = g
  +c = c
  +ts = ts
  +p = p
  +t = t
  +h = h
  clash(P.member(~K, ~eq, c, t), hct,
    Laws.plan_cycle(~K, ~eq, ~sound, g, c, hc, ts, p, t, h, Laws.plan_targets(~K, ~eq, ~sound, g, ts, p, t, h, ht)))

# Invalidation
# ------------

def or_true_l(a: Bool, -b: Bool, ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool}, false_ne_true(ha))

def or_true_r(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def or_mono(a: Bool, -b: Bool, -c: Bool, h: {Bool.or(a, b) == True{} : Bool}, f: {b == True{} : Bool} -> {c == True{} : Bool}) ->
  {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

def imp_true(a: Bool, -b: Bool, ha: {a == True{} : Bool}, h: {Bool.or(Bool.not(a), b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(ha))

def Hit(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>, +y: K) -> Bool:
  Bool.or(P.member(~K, ~eq, changed, y), P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), acc))

def Acc(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>, +y: K) -> List<&2, K>:
  P.invalidate.if(K, Hit(~K, ~eq, g, changed, acc, y), y, acc)

def IG(~K: Data, ~eq: K -> K -> Bool, p: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>) -> List<&2, K>:
  P.invalidate.go(~K, ~eq, p, g, changed, acc)

def inv_if_mono(~K: Data, ~eq: K -> K -> Bool, c: Bool, +y: K, +acc: List<&2, K>, +k: K, h: {P.member(~K, ~eq, acc, k) == True{} : Bool}) ->
  {P.member(~K, ~eq, P.invalidate.if(K, c, y, acc), k) == True{} : Bool}:
  match c:
    case True{}:
      mem_cons_r(~K, ~eq, y, acc, k, h)
    case False{}:
      h

def inv_if_hit(~K: Data, ~eq: K -> K -> Bool, c: Bool, +y: K, +acc: List<&2, K>, +k: K, hc: {c == True{} : Bool}, he: {eq(k, y) == True{} : Bool}) ->
  {P.member(~K, ~eq, P.invalidate.if(K, c, y, acc), k) == True{} : Bool}:
  match c:
    case True{}:
      mem_hit(~K, ~eq, y, acc, k, he)
    case False{}:
      Empty.absurd({P.member(~K, ~eq, acc, k) == True{} : Bool}, false_ne_true(hc))

def inv_if_miss(~K: Data, ~eq: K -> K -> Bool, c: Bool, +y: K, +acc: List<&2, K>, +k: K, he: {eq(k, y) == False{} : Bool},
  h: {P.member(~K, ~eq, P.invalidate.if(K, c, y, acc), k) == True{} : Bool}
) -> {P.member(~K, ~eq, acc, k) == True{} : Bool}:
  match c:
    case True{}:
      mem_tail(~K, ~eq, y, acc, k, he, h)
    case False{}:
      h

def inv_if_false(~K: Data, ~eq: K -> K -> Bool, c: Bool, +y: K, +acc: List<&2, K>, +k: K, hc: {c == False{} : Bool},
  h: {P.member(~K, ~eq, P.invalidate.if(K, c, y, acc), k) == True{} : Bool}
) -> {P.member(~K, ~eq, acc, k) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({P.member(~K, ~eq, acc, k) == True{} : Bool}, true_ne_false(hc))
    case False{}:
      h

def inv_if_all(~K: Data, ~eq: K -> K -> Bool, c: Bool, +y: K, +acc: List<&2, K>, +s: List<&2, K>,
  hy: {c == True{} : Bool} -> {P.member(~K, ~eq, s, y) == True{} : Bool}, ha: {P.all_in(~K, ~eq, acc, s) == True{} : Bool}
) -> {P.all_in(~K, ~eq, P.invalidate.if(K, c, y, acc), s) == True{} : Bool}:
  match c:
    case True{}:
      and_true(P.member(~K, ~eq, s, y), P.all_in(~K, ~eq, acc, s), hy({==}), ha)
    case False{}:
      ha

# Invalidation never drops a stale node.
def inv_mono(~K: Data, ~eq: K -> K -> Bool, p: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>, +k: K,
  h: {P.member(~K, ~eq, acc, k) == True{} : Bool}
) -> {P.member(~K, ~eq, IG(~K, ~eq, p, g, changed, acc), k) == True{} : Bool}:
  match p:
    case Nil{}:
      h
    case Con{+y, t}:
      inv_mono(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y), k, inv_if_mono(~K, ~eq, Hit(~K, ~eq, g, changed, acc, y), y, acc, k, h))

def mem_move(~K: Data, ~eq: K -> K -> Bool, +xs: List<&2, K>, +x: K, +y: K, e: {x == y : K}, h: {P.member(~K, ~eq, xs, x) == True{} : Bool}) ->
  {P.member(~K, ~eq, xs, y) == True{} : Bool}:
  Equal.trans(Bool, P.member(~K, ~eq, xs, y), P.member(~K, ~eq, xs, x), True{},
    Equal.cong(K, Bool, z => P.member(~K, ~eq, xs, z), y, x, Equal.sym(K, x, y, e)), h)

def changed_go.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>,
  +acc: List<&2, K>, +x: K,
  +hb: {eq(x, y) == b : Bool}, hx: {P.member(~K, ~eq, y <> t, x) == True{} : Bool}, hc: {P.member(~K, ~eq, changed, x) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, x) == True{} : Bool} -> {P.member(~K, ~eq, IG(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y)), x) == True{} : Bool}
) -> {P.member(~K, ~eq, IG(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y)), x) == True{} : Bool}:
  match b:
    case True{}:
      inv_mono(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y), x,
        inv_if_hit(~K, ~eq, Hit(~K, ~eq, g, changed, acc, y), y, acc, x,
          or_true_l(P.member(~K, ~eq, changed, y), P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), acc),
            mem_move(~K, ~eq, changed, x, y, sound(x, y, hb), hc)),
          hb))
    case False{}:
      ih(mem_tail(~K, ~eq, y, t, x, hb, hx))

def changed_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>, +x: K,
  hx: {P.member(~K, ~eq, p, x) == True{} : Bool}, hc: {P.member(~K, ~eq, changed, x) == True{} : Bool}
) -> {P.member(~K, ~eq, IG(~K, ~eq, p, g, changed, acc), x) == True{} : Bool}:
  match p:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, acc, x) == True{} : Bool}, false_ne_true(hx))
    case Con{+y, +t}:
      +hc = hc
      changed_go.if(~K, ~eq, ~sound, eq(x, y), y, t, g, changed, acc, x, {==}, hx, hc,
        hm => changed_go(~K, ~eq, ~sound, t, g, changed, Acc(~K, ~eq, g, changed, acc, y), x, hm, hc))

def Laws.stale_changed(K, eq, sound, p, g, changed, x, hx, hc):
  changed_go(~K, ~eq, ~sound, p, g, changed, Nil{}, x, hx, hc)

def ord_notin.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +z: K, +r: List<&2, K>, +done: List<&2, K>, +d: K,
  hb: {eq(d, z) == b : Bool}, hz: {P.member(~K, ~eq, done, z) == False{} : Bool}, hd: {P.member(~K, ~eq, done, d) == True{} : Bool},
  ih: {P.member(~K, ~eq, r, d) == False{} : Bool}
) -> {P.member(~K, ~eq, z <> r, d) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({P.member(~K, ~eq, z <> r, d) == False{} : Bool},
        clash(P.member(~K, ~eq, done, z), mem_move(~K, ~eq, done, d, z, sound(d, z, hb), hd), hz))
    case False{}:
      mem_cons_false(~K, ~eq, z, r, d, hb, ih)

# A done node does not come again.
def ord_notin(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), t: List<&2, K>, +g: List<&2, P.Node<K>>, +done: List<&2, K>, +d: K,
  hO: {P.ordered(~K, ~eq, t, g, done) == True{} : Bool}, hd: {P.member(~K, ~eq, done, d) == True{} : Bool}
) -> {P.member(~K, ~eq, t, d) == False{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      +hO = hO
      +hd = hd
      ord_notin.if(~K, ~eq, ~sound, eq(d, z), z, r, done, d, {==}, ord_fresh(~K, ~eq, z, r, g, done, hO), hd,
        ord_notin(~K, ~eq, ~sound, r, g, z <> done, d, ord_rest(~K, ~eq, z, r, g, done, hO), mem_cons_r(~K, ~eq, z, done, d, hd)))

def inv_notin.if(
  ~K: Data, ~eq: K -> K -> Bool, b: Bool, +z: K, +r: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>, +d: K,
  +hb: {eq(d, z) == b : Bool}, hn: {P.member(~K, ~eq, z <> r, d) == False{} : Bool},
  ih: {P.member(~K, ~eq, r, d) == False{} : Bool} -> {P.member(~K, ~eq, Acc(~K, ~eq, g, changed, acc, z), d) == True{} : Bool}
) -> {P.member(~K, ~eq, acc, d) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({P.member(~K, ~eq, acc, d) == True{} : Bool}, clash(P.member(~K, ~eq, z <> r, d), mem_hit(~K, ~eq, z, r, d, hb), hn))
    case False{}:
      inv_if_miss(~K, ~eq, Hit(~K, ~eq, g, changed, acc, z), z, acc, d, hb, ih(mem_tail_false(~K, ~eq, z, r, d, hb, hn)))

# Invalidation adds only nodes of p.
def inv_notin(
  ~K: Data, ~eq: K -> K -> Bool, t: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>, +d: K,
  hn: {P.member(~K, ~eq, t, d) == False{} : Bool}, hs: {P.member(~K, ~eq, IG(~K, ~eq, t, g, changed, acc), d) == True{} : Bool}
) -> {P.member(~K, ~eq, acc, d) == True{} : Bool}:
  match t:
    case Nil{}:
      hs
    case Con{+z, +r}:
      inv_notin.if(~K, ~eq, eq(d, z), z, r, g, changed, acc, d, {==}, hn,
        h => inv_notin(~K, ~eq, r, g, changed, Acc(~K, ~eq, g, changed, acc, z), d, h, hs))

def any_in_intro.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +w: K, +t: List<&2, K>, +acc: List<&2, K>, +d: K,
  +hb: {eq(d, w) == b : Bool}, hm: {P.member(~K, ~eq, w <> t, d) == True{} : Bool}, ha: {P.member(~K, ~eq, acc, d) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, d) == True{} : Bool} -> {P.any_in(~K, ~eq, t, acc) == True{} : Bool}
) -> {P.any_in(~K, ~eq, w <> t, acc) == True{} : Bool}:
  match b:
    case True{}:
      or_true_l(P.member(~K, ~eq, acc, w), P.any_in(~K, ~eq, t, acc), mem_move(~K, ~eq, acc, d, w, sound(d, w, hb), ha))
    case False{}:
      or_true_r(P.member(~K, ~eq, acc, w), P.any_in(~K, ~eq, t, acc), ih(mem_tail(~K, ~eq, w, t, d, hb, hm)))

def any_in_intro(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), ds: List<&2, K>, +acc: List<&2, K>, +d: K,
  hm: {P.member(~K, ~eq, ds, d) == True{} : Bool}, ha: {P.member(~K, ~eq, acc, d) == True{} : Bool}
) -> {P.any_in(~K, ~eq, ds, acc) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(hm))
    case Con{+w, +t}:
      +ha = ha
      any_in_intro.if(~K, ~eq, ~sound, eq(d, w), w, t, acc, d, {==}, hm, ha, h => any_in_intro(~K, ~eq, ~sound, t, acc, d, h, ha))

def deps_move(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +x: K, +y: K, -ds: List<&2, K>, e: {x == y : K},
  hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>}
) -> {P.deps(~K, ~eq, g, y) == Some{ds} : Maybe<&2, List<&2, K>>}:
  Equal.trans(Maybe<&2, List<&2, K>>, P.deps(~K, ~eq, g, y), P.deps(~K, ~eq, g, x), Some{ds},
    Equal.cong(K, Maybe<&2, List<&2, K>>, z => P.deps(~K, ~eq, g, z), y, x, Equal.sym(K, x, y, e)), hd)

def or_nil_some(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +y: K, +ds: List<&2, K>,
  hd: {P.deps(~K, ~eq, g, y) == Some{ds} : Maybe<&2, List<&2, K>>}
) -> {P.deps.or_nil(~K, ~eq, g, y) == ds : List<&2, K>}:
  Equal.cong(Maybe<&2, List<&2, K>>, List<&2, K>, m => Maybe.default(&2, List<&2, K>, m, Nil{}), P.deps(~K, ~eq, g, y), Some{ds}, hd)

def dep_go.hit(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), cv: Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>,
  +acc: List<&2, K>, +x: K, +ds: List<&2, K>, +d: K,
  +hcv: {Hit(~K, ~eq, g, changed, acc, y) == cv : Bool}, hb: {eq(x, y) == True{} : Bool},
  hdy: {P.deps(~K, ~eq, g, y) == Some{ds} : Maybe<&2, List<&2, K>>}, hm: {P.member(~K, ~eq, ds, d) == True{} : Bool},
  had: {P.member(~K, ~eq, Acc(~K, ~eq, g, changed, acc, y), d) == True{} : Bool}
) -> {P.member(~K, ~eq, IG(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y)), x) == True{} : Bool}:
  match cv:
    case True{}:
      inv_mono(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y), x,
        inv_if_hit(~K, ~eq, Hit(~K, ~eq, g, changed, acc, y), y, acc, x, hcv, hb))
    case False{}:
      +dn = P.deps.or_nil(~K, ~eq, g, y)
      Empty.absurd({P.member(~K, ~eq, IG(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y)), x) == True{} : Bool},
        clash(P.any_in(~K, ~eq, dn, acc),
          (%Equal.sym(List<&2, K>, P.deps.or_nil(~K, ~eq, g, y), ds, or_nil_some(~K, ~eq, g, y, ds, hdy)) : {P.any_in(~K, ~eq, _, acc) == True{} : Bool}
           any_in_intro(~K, ~eq, ~sound, ds, acc, d, hm, inv_if_false(~K, ~eq, Hit(~K, ~eq, g, changed, acc, y), y, acc, d, hcv, had))),
          or_false_r(P.member(~K, ~eq, changed, y), P.any_in(~K, ~eq, dn, acc), hcv)))

def dep_go.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>,
  +done: List<&2, K>, +acc: List<&2, K>, +x: K, +ds: List<&2, K>, +d: K,
  +hb: {eq(x, y) == b : Bool}, hO: {P.ordered(~K, ~eq, y <> t, g, done) == True{} : Bool}, hx: {P.member(~K, ~eq, y <> t, x) == True{} : Bool},
  hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>}, hm: {P.member(~K, ~eq, ds, d) == True{} : Bool},
  hs: {P.member(~K, ~eq, IG(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y)), d) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, x) == True{} : Bool} -> {P.member(~K, ~eq, IG(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y)), x) == True{} : Bool}
) -> {P.member(~K, ~eq, IG(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y)), x) == True{} : Bool}:
  match b:
    case True{}:
      +hO = hO
      +hm = hm
      +hdy = deps_move(~K, ~eq, g, x, y, ds, sound(x, y, hb), hd)
      +hdone = all_in_mem(~K, ~eq, ~sound, ds, done, d, node_all(~K, ~eq, g, y, ds, done, hdy, ord_node(~K, ~eq, y, t, g, done, hO)), hm)
      +hnt = ord_notin(~K, ~eq, ~sound, t, g, y <> done, d, ord_rest(~K, ~eq, y, t, g, done, hO), mem_cons_r(~K, ~eq, y, done, d, hdone))
      dep_go.hit(~K, ~eq, ~sound, Hit(~K, ~eq, g, changed, acc, y), y, t, g, changed, acc, x, ds, d, {==}, hb, hdy, hm,
        inv_notin(~K, ~eq, t, g, changed, Acc(~K, ~eq, g, changed, acc, y), d, hnt, hs))
    case False{}:
      ih(mem_tail(~K, ~eq, y, t, x, hb, hx))

# In an ordered p, a node that requires a stale node is stale.
def dep_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>,
  +done: List<&2, K>, +acc: List<&2, K>, +x: K, +ds: List<&2, K>, +d: K,
  hO: {P.ordered(~K, ~eq, p, g, done) == True{} : Bool}, hx: {P.member(~K, ~eq, p, x) == True{} : Bool},
  hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>}, hm: {P.member(~K, ~eq, ds, d) == True{} : Bool},
  hs: {P.member(~K, ~eq, IG(~K, ~eq, p, g, changed, acc), d) == True{} : Bool}
) -> {P.member(~K, ~eq, IG(~K, ~eq, p, g, changed, acc), x) == True{} : Bool}:
  match p:
    case Nil{}:
      Empty.absurd({P.member(~K, ~eq, acc, x) == True{} : Bool}, false_ne_true(hx))
    case Con{+y, +t}:
      +hO = hO
      +hd = hd
      +hm = hm
      +hs = hs
      dep_go.if(~K, ~eq, ~sound, eq(x, y), y, t, g, changed, done, acc, x, ds, d, {==}, hO, hx, hd, hm, hs,
        h => dep_go(~K, ~eq, ~sound, t, g, changed, y <> done, Acc(~K, ~eq, g, changed, acc, y), x, ds, d,
          ord_rest(~K, ~eq, y, t, g, done, hO), h, hd, hm, hs))

def Laws.stale_dependents(K, eq, sound, g, ts, p, changed, x, ds, d, h, hx, hd, hm, hs):
  +g = g
  +ts = ts
  +p = p
  dep_go(~K, ~eq, ~sound, p, g, changed, Nil{}, Nil{}, x, ds, d, plan_ordered(~K, ~eq, g, ts, p, h), hx, hd, hm, hs)

def any_in_mono.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +w: K, +t: List<&2, K>, +a: List<&2, K>, +s: List<&2, K>,
  hb: {P.member(~K, ~eq, a, w) == b : Bool}, hab: {P.all_in(~K, ~eq, a, s) == True{} : Bool},
  h: {Bool.or(b, P.any_in(~K, ~eq, t, a)) == True{} : Bool},
  ih: {P.any_in(~K, ~eq, t, a) == True{} : Bool} -> {P.any_in(~K, ~eq, t, s) == True{} : Bool}
) -> {P.any_in(~K, ~eq, w <> t, s) == True{} : Bool}:
  match b:
    case True{}:
      or_true_l(P.member(~K, ~eq, s, w), P.any_in(~K, ~eq, t, s), all_in_mem(~K, ~eq, ~sound, a, s, w, hab, hb))
    case False{}:
      or_true_r(P.member(~K, ~eq, s, w), P.any_in(~K, ~eq, t, s), ih(h))

def any_in_mono(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), xs: List<&2, K>, +a: List<&2, K>, +s: List<&2, K>,
  hab: {P.all_in(~K, ~eq, a, s) == True{} : Bool}, h: {P.any_in(~K, ~eq, xs, a) == True{} : Bool}
) -> {P.any_in(~K, ~eq, xs, s) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+w, +t}:
      +hab = hab
      any_in_mono.if(~K, ~eq, ~sound, P.member(~K, ~eq, a, w), w, t, a, s, {==}, hab, h,
        hh => any_in_mono(~K, ~eq, ~sound, t, a, s, hab, hh))

def Up(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +s: List<&2, K>, +y: K) -> Bool:
  Bool.or(P.member(~K, ~eq, changed, y), P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), s))

# Every stale node is in a set closed under the invalidation rule on p.
def sub_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +changed: List<&2, K>, +acc: List<&2, K>,
  +s: List<&2, K>, hup: {Laws.upward(~K, ~eq, p, g, changed, s) == True{} : Bool}, hacc: {P.all_in(~K, ~eq, acc, s) == True{} : Bool}
) -> {P.all_in(~K, ~eq, IG(~K, ~eq, p, g, changed, acc), s) == True{} : Bool}:
  match p:
    case Nil{}:
      hacc
    case Con{+y, t}:
      +hup = hup
      +hacc = hacc
      +head = Bool.or(Bool.not(Up(~K, ~eq, g, changed, s, y)), P.member(~K, ~eq, s, y))
      sub_go(~K, ~eq, ~sound, t, g, changed, Acc(~K, ~eq, g, changed, acc, y), s,
        and_r(head, Laws.upward(~K, ~eq, t, g, changed, s), hup),
        inv_if_all(~K, ~eq, Hit(~K, ~eq, g, changed, acc, y), y, acc, s,
          hc => imp_true(Up(~K, ~eq, g, changed, s, y), P.member(~K, ~eq, s, y),
            or_mono(P.member(~K, ~eq, changed, y), P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), acc), P.any_in(~K, ~eq, P.deps.or_nil(~K, ~eq, g, y), s), hc,
              ha => any_in_mono(~K, ~eq, ~sound, P.deps.or_nil(~K, ~eq, g, y), acc, s, hacc, ha)),
            and_l(head, Laws.upward(~K, ~eq, t, g, changed, s), hup)),
          hacc))

def Laws.stale_least(K, eq, sound, p, g, changed, s, hs, x, hx):
  +p = p
  +g = g
  +changed = changed
  +s = s
  all_in_mem(~K, ~eq, ~sound, IG(~K, ~eq, p, g, changed, Nil{}), s, x, sub_go(~K, ~eq, ~sound, p, g, changed, Nil{}, s, hs, {==}), hx)

# Execution
# ---------

def St(~K: Data, ~eq: K -> K -> Bool, +st: List<&2, P.Entry<K>>, +k: K) -> Maybe<&2, P.Status>:
  P.status(~K, ~eq, st, k)

def st_hit(~K: Data, ~eq: K -> K -> Bool, +x: K, +s: P.Status, +t: List<&2, P.Entry<K>>, +k: K, e: {eq(k, x) == True{} : Bool}) ->
  {St(~K, ~eq, P.Entry{x, s} <> t, k) == Some{s} : Maybe<&2, P.Status>}:
  %Equal.sym(Bool, eq(k, x), True{}, e) : {P.when(Maybe<&2, P.Status>, u => P.status(~K, ~eq, t, k), _, Some{s}) == Some{s} : Maybe<&2, P.Status>}
  {==}

def st_miss(~K: Data, ~eq: K -> K -> Bool, +x: K, +s: P.Status, +t: List<&2, P.Entry<K>>, +k: K, e: {eq(k, x) == False{} : Bool}) ->
  {St(~K, ~eq, P.Entry{x, s} <> t, k) == St(~K, ~eq, t, k) : Maybe<&2, P.Status>}:
  %Equal.sym(Bool, eq(k, x), False{}, e) : {P.when(Maybe<&2, P.Status>, u => P.status(~K, ~eq, t, k), _, Some{s}) == P.status(~K, ~eq, t, k) : Maybe<&2, P.Status>}
  {==}

def NotFresh(s: P.Status) -> Type:
  match s:
    case P.Fresh{}:
      Empty
    case _:
      Unit

def skipped_ne_fresh(e: {P.Skipped{} == P.Fresh{} : P.Status}) -> Empty:
  %e : NotFresh(_)
  Unit{}

def outcome_ne_fresh(rs: List<&2, Bool>, e: {P.outcome(rs) == P.Fresh{} : P.Status}) -> Empty:
  match rs:
    case Nil{}:
      %e : NotFresh(_)
      Unit{}
    case Con{b, t}:
      match b:
        case True{}:
          %e : NotFresh(_)
          Unit{}
        case False{}:
          %e : NotFresh(_)
          Unit{}

def none_of(m: Maybe<&2, P.Status>, h: {Maybe.is_some(&2, P.Status, m) == False{} : Bool}) -> {m == None{} : Maybe<&2, P.Status>}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      Empty.absurd({Some{s} == None{} : Maybe<&2, P.Status>}, true_ne_false(h))

# What a decision tells about the state it was made in.
def View(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +y: K, m: Maybe<&2, P.Status>) -> Type:
  match m:
    case None{}:
      {Maybe.is_some(&2, P.Status, St(~K, ~eq, st, y)) == True{} : Bool}
    case Some{+s}:
      {St(~K, ~eq, st, y) == None{} : Maybe<&2, P.Status>}
      & ((@ds: List<&2, K> -> {P.Status.selected(s) == True{} : Bool} -> {P.deps(~K, ~eq, g, y) == Some{ds} : Maybe<&2, List<&2, K>>} -> {P.ready(~K, ~eq, ds, st) == True{} : Bool})
      & ({s == P.Fresh{} : P.Status} -> {P.member(~K, ~eq, stale, y) == False{} : Bool}))

def ready_move(
  ~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +st: List<&2, P.Entry<K>>, +y: K, +dy: List<&2, K>, +ds: List<&2, K>,
  hdy: {P.deps(~K, ~eq, g, y) == Some{dy} : Maybe<&2, List<&2, K>>}, hd: {P.deps(~K, ~eq, g, y) == Some{ds} : Maybe<&2, List<&2, K>>},
  hr: {P.ready(~K, ~eq, dy, st) == True{} : Bool}
) -> {P.ready(~K, ~eq, ds, st) == True{} : Bool}:
  %some_inj(List<&2, K>, dy, ds, Equal.trans(Maybe<&2, List<&2, K>>, Some{dy}, P.deps(~K, ~eq, g, y), Some{ds},
    Equal.sym(Maybe<&2, List<&2, K>>, P.deps(~K, ~eq, g, y), Some{dy}, hdy), hd)) : {P.ready(~K, ~eq, _, st) == True{} : Bool}
  hr

def view.ready(
  ~K: Data, ~eq: K -> K -> Bool, r: Bool, sx: Bool, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +y: K,
  +dy: List<&2, K>, rs: List<&2, Bool>,
  +hr: {P.ready(~K, ~eq, dy, st) == r : Bool}, hsx: {P.member(~K, ~eq, stale, y) == sx : Bool},
  +hdy: {P.deps(~K, ~eq, g, y) == Some{dy} : Maybe<&2, List<&2, K>>}, +hn: {St(~K, ~eq, st, y) == None{} : Maybe<&2, P.Status>}
) -> View(~K, ~eq, g, stale, st, y, P.Action.status(P.decide.ready(r, sx), rs)):
  match r sx:
    case False{} _:
      (hn, (ds => hs => hd => Empty.absurd({P.ready(~K, ~eq, ds, st) == True{} : Bool}, false_ne_true(hs)),
        e => Empty.absurd({P.member(~K, ~eq, stale, y) == False{} : Bool}, skipped_ne_fresh(e))))
    case True{} True{}:
      (hn, (ds => hs => hd => ready_move(~K, ~eq, g, st, y, dy, ds, hdy, hd, hr),
        e => Empty.absurd({P.member(~K, ~eq, stale, y) == False{} : Bool}, outcome_ne_fresh(rs, e))))
    case True{} False{}:
      (hn, (ds => hs => hd => ready_move(~K, ~eq, g, st, y, dy, ds, hdy, hd, hr), e => hsx))

def view.node(
  ~K: Data, ~eq: K -> K -> Bool, mn: Maybe<&2, List<&2, K>>, +sx: Bool, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +y: K,
  rs: List<&2, Bool>,
  hmn: {P.deps(~K, ~eq, g, y) == mn : Maybe<&2, List<&2, K>>}, hsx: {P.member(~K, ~eq, stale, y) == sx : Bool},
  +hn: {St(~K, ~eq, st, y) == None{} : Maybe<&2, P.Status>}
) -> View(~K, ~eq, g, stale, st, y, P.Action.status(P.decide.node(~K, ~eq, mn, sx, st), rs)):
  match mn:
    case None{}:
      (hn, (ds => hs => hd => Empty.absurd({P.ready(~K, ~eq, ds, st) == True{} : Bool}, false_ne_true(hs)),
        e => Empty.absurd({P.member(~K, ~eq, stale, y) == False{} : Bool}, skipped_ne_fresh(e))))
    case Some{+dy}:
      view.ready(~K, ~eq, P.ready(~K, ~eq, dy, st), sx, g, stale, st, y, dy, rs, {==}, hsx, hmn, hn)

def view.seen(
  ~K: Data, ~eq: K -> K -> Bool, b: Bool, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +y: K, rs: List<&2, Bool>,
  hb: {Maybe.is_some(&2, P.Status, St(~K, ~eq, st, y)) == b : Bool}
) -> View(~K, ~eq, g, stale, st, y, P.Action.status(P.decide.seen(~K, ~eq, b, g, stale, st, y), rs)):
  match b:
    case True{}:
      hb
    case False{}:
      view.node(~K, ~eq, P.deps(~K, ~eq, g, y), P.member(~K, ~eq, stale, y), g, stale, st, y, rs, {==}, {==},
        none_of(St(~K, ~eq, st, y), hb))

def view(~K: Data, ~eq: K -> K -> Bool, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +y: K, rs: List<&2, Bool>) ->
  View(~K, ~eq, g, stale, st, y, P.Action.status(P.decide(~K, ~eq, g, stale, st, y), rs)):
  view.seen(~K, ~eq, Maybe.is_some(&2, P.Status, St(~K, ~eq, st, y)), g, stale, st, y, rs, {==})

def ok_keep.m(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +y: K, +s: P.Status, +st: List<&2, P.Entry<K>>, +d: K,
  hc: {eq(d, y) == c : Bool}, h: {P.ok.at(St(~K, ~eq, st, d)) == True{} : Bool}, hn: {St(~K, ~eq, st, y) == None{} : Maybe<&2, P.Status>}
) -> {P.ok.at(St(~K, ~eq, P.Entry{y, s} <> st, d)) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({P.ok.at(St(~K, ~eq, P.Entry{y, s} <> st, d)) == True{} : Bool},
        false_ne_true(
          (%hn : {P.ok.at(_) == True{} : Bool}
           (%sound(d, y, hc) : {P.ok.at(St(~K, ~eq, st, _)) == True{} : Bool}
            h))))
    case False{}:
      %Equal.sym(Maybe<&2, P.Status>, St(~K, ~eq, P.Entry{y, s} <> st, d), St(~K, ~eq, st, d), st_miss(~K, ~eq, y, s, st, d, hc)) :
        {P.ok.at(_) == True{} : Bool}
      h

def ready_keep(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), ds: List<&2, K>, +st: List<&2, P.Entry<K>>, +y: K, +s: P.Status,
  hr: {P.ready(~K, ~eq, ds, st) == True{} : Bool}, +hn: {St(~K, ~eq, st, y) == None{} : Maybe<&2, P.Status>}
) -> {P.ready(~K, ~eq, ds, P.Entry{y, s} <> st) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      +hr = hr
      and_true(P.ok.at(St(~K, ~eq, P.Entry{y, s} <> st, d)), P.ready(~K, ~eq, t, P.Entry{y, s} <> st),
        ok_keep.m(~K, ~eq, ~sound, eq(d, y), y, s, st, d, {==}, and_l(P.ok.at(St(~K, ~eq, st, d)), P.ready(~K, ~eq, t, st), hr), hn),
        ready_keep(~K, ~eq, ~sound, t, st, y, s, and_r(P.ok.at(St(~K, ~eq, st, d)), P.ready(~K, ~eq, t, st), hr), hn))

def Inv.ready(~K: Data, ~eq: K -> K -> Bool, +st: List<&2, P.Entry<K>>, +x: K, +ds: List<&2, K>) -> Type:
  {P.selected.at(St(~K, ~eq, st, x)) == True{} : Bool} -> {P.ready(~K, ~eq, ds, st) == True{} : Bool}

def ready_step.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +g: List<&2, P.Node<K>>, +st: List<&2, P.Entry<K>>, +y: K, +s: P.Status,
  +x: K, +ds: List<&2, K>,
  +hc: {eq(x, y) == c : Bool}, hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>},
  +hn: {St(~K, ~eq, st, y) == None{} : Maybe<&2, P.Status>},
  hrd: @ds: List<&2, K> -> {P.Status.selected(s) == True{} : Bool} -> {P.deps(~K, ~eq, g, y) == Some{ds} : Maybe<&2, List<&2, K>>} -> {P.ready(~K, ~eq, ds, st) == True{} : Bool},
  inv: Inv.ready(~K, ~eq, st, x, ds),
  hsel: {P.selected.at(St(~K, ~eq, P.Entry{y, s} <> st, x)) == True{} : Bool}
) -> {P.ready(~K, ~eq, ds, P.Entry{y, s} <> st) == True{} : Bool}:
  match c:
    case True{}:
      ready_keep(~K, ~eq, ~sound, ds, st, y, s,
        hrd(ds,
          (%st_hit(~K, ~eq, y, s, st, x, hc) : {P.selected.at(_) == True{} : Bool}
           hsel),
          deps_move(~K, ~eq, g, x, y, ds, sound(x, y, hc), hd)),
        hn)
    case False{}:
      ready_keep(~K, ~eq, ~sound, ds, st, y, s,
        inv(%st_miss(~K, ~eq, y, s, st, x, hc) : {P.selected.at(_) == True{} : Bool}
          hsel),
        hn)

def ready_step(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), m: Maybe<&2, P.Status>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>,
  +st: List<&2, P.Entry<K>>, +y: K, +x: K, +ds: List<&2, K>,
  hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>}, hv: View(~K, ~eq, g, stale, st, y, m), inv: Inv.ready(~K, ~eq, st, x, ds)
) -> Inv.ready(~K, ~eq, P.record(K, m, st, y), x, ds):
  match m:
    case None{}:
      inv
    case Some{+s}:
      (hn, rest) = hv
      (hrd, hfr) = rest
      hsel => ready_step.if(~K, ~eq, ~sound, eq(x, y), g, st, y, s, x, ds, {==}, hd, hn, hrd, inv, hsel)

def ready_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>,
  +st: List<&2, P.Entry<K>>, +rs: List<&2, Bool>, +x: K, +ds: List<&2, K>,
  +hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>}, inv: Inv.ready(~K, ~eq, st, x, ds)
) -> Inv.ready(~K, ~eq, P.exec(~K, ~eq, p, g, stale, st, rs), x, ds):
  match p:
    case Nil{}:
      inv
    case Con{+y, t}:
      +a = P.decide(~K, ~eq, g, stale, st, y)
      ready_go(~K, ~eq, ~sound, t, g, stale, P.step(K, a, st, y, rs), P.step.rest(a, rs), x, ds, hd,
        ready_step(~K, ~eq, ~sound, P.Action.status(a, rs), g, stale, st, y, x, ds, hd, view(~K, ~eq, g, stale, st, y, rs), inv))

def Laws.exec_ready(K, eq, sound, p, g, stale, rs, x, ds, hx, hd):
  ready_go(~K, ~eq, ~sound, p, g, stale, Nil{}, rs, x, ds, hd,
    h => Empty.absurd({P.ready(~K, ~eq, ds, Nil{}) == True{} : Bool}, false_ne_true(h)))(hx)

def ok_sel(m: Maybe<&2, P.Status>, h: {P.ok.at(m) == True{} : Bool}) -> {P.selected.at(m) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{s}:
      match s:
        case P.Built{}:
          {==}
        case P.Fresh{}:
          {==}
        case P.Failed{}:
          Empty.absurd({True{} == True{} : Bool}, false_ne_true(h))
        case P.Skipped{}:
          Empty.absurd({False{} == True{} : Bool}, false_ne_true(h))

def ready_mem.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +w: K, +t: List<&2, K>, +st: List<&2, P.Entry<K>>, +d: K,
  hc: {eq(d, w) == c : Bool}, hw: {P.ok.at(St(~K, ~eq, st, w)) == True{} : Bool}, hm: {P.member(~K, ~eq, w <> t, d) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, d) == True{} : Bool} -> {P.ok.at(St(~K, ~eq, st, d)) == True{} : Bool}
) -> {P.ok.at(St(~K, ~eq, st, d)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(K, d, w, sound(d, w, hc)) : {P.ok.at(St(~K, ~eq, st, _)) == True{} : Bool}
      hw
    case False{}:
      ih(mem_tail(~K, ~eq, w, t, d, hc, hm))

def ready_mem(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), ds: List<&2, K>, +st: List<&2, P.Entry<K>>, +d: K,
  hr: {P.ready(~K, ~eq, ds, st) == True{} : Bool}, hm: {P.member(~K, ~eq, ds, d) == True{} : Bool}
) -> {P.ok.at(St(~K, ~eq, st, d)) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({P.ok.at(St(~K, ~eq, st, d)) == True{} : Bool}, false_ne_true(hm))
    case Con{+w, +t}:
      +hr = hr
      ready_mem.if(~K, ~eq, ~sound, eq(d, w), w, t, st, d, {==},
        and_l(P.ok.at(St(~K, ~eq, st, w)), P.ready(~K, ~eq, t, st), hr), hm,
        h => ready_mem(~K, ~eq, ~sound, t, st, d, and_r(P.ok.at(St(~K, ~eq, st, w)), P.ready(~K, ~eq, t, st), hr), h))

def blocked.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), b: Bool, +p: List<&2, K>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +rs: List<&2, Bool>,
  +x: K, +ds: List<&2, K>, +d: K,
  hb: {P.ok.at(St(~K, ~eq, Laws.run(~K, ~eq, p, g, stale, rs), x)) == b : Bool},
  hd: {P.deps(~K, ~eq, g, x) == Some{ds} : Maybe<&2, List<&2, K>>}, hm: {P.member(~K, ~eq, ds, d) == True{} : Bool},
  hf: {P.ok.at(St(~K, ~eq, Laws.run(~K, ~eq, p, g, stale, rs), d)) == False{} : Bool}
) -> {b == False{} : Bool}:
  match b:
    case True{}:
      +f = Laws.run(~K, ~eq, p, g, stale, rs)
      Empty.absurd({True{} == False{} : Bool},
        clash(P.ok.at(St(~K, ~eq, f, d)),
          ready_mem(~K, ~eq, ~sound, ds, f, d,
            Laws.exec_ready(~K, ~eq, ~sound, p, g, stale, rs, x, ds, ok_sel(St(~K, ~eq, f, x), hb), hd), hm),
          hf))
    case False{}:
      {==}

def Laws.exec_blocked(K, eq, sound, p, g, stale, rs, x, ds, d, hd, hm, hf):
  +p = p
  +g = g
  +stale = stale
  +rs = rs
  +x = x
  blocked.if(~K, ~eq, ~sound, P.ok.at(St(~K, ~eq, Laws.run(~K, ~eq, p, g, stale, rs), x)), p, g, stale, rs, x, ds, d, {==}, hd, hm, hf)

def keys_none.if(
  ~K: Data, ~eq: K -> K -> Bool, c: Bool, +z: K, +v: P.Status, +t: List<&2, P.Entry<K>>, +y: K,
  +hc: {eq(y, z) == c : Bool}, h: {St(~K, ~eq, P.Entry{z, v} <> t, y) == None{} : Maybe<&2, P.Status>},
  ih: {St(~K, ~eq, t, y) == None{} : Maybe<&2, P.Status>} -> {P.member(~K, ~eq, P.keys(K, t), y) == False{} : Bool}
) -> {P.member(~K, ~eq, z <> P.keys(K, t), y) == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({P.member(~K, ~eq, z <> P.keys(K, t), y) == False{} : Bool},
        none_ne_some(P.Status, v, Equal.trans(Maybe<&2, P.Status>, None{}, St(~K, ~eq, P.Entry{z, v} <> t, y), Some{v},
          Equal.sym(Maybe<&2, P.Status>, St(~K, ~eq, P.Entry{z, v} <> t, y), None{}, h), st_hit(~K, ~eq, z, v, t, y, hc))))
    case False{}:
      mem_cons_false(~K, ~eq, z, P.keys(K, t), y, hc,
        ih(Equal.trans(Maybe<&2, P.Status>, St(~K, ~eq, t, y), St(~K, ~eq, P.Entry{z, v} <> t, y), None{},
          Equal.sym(Maybe<&2, P.Status>, St(~K, ~eq, P.Entry{z, v} <> t, y), St(~K, ~eq, t, y), st_miss(~K, ~eq, z, v, t, y, hc)), h)))

# A node with no status is not a key.
def keys_none(
  ~K: Data, ~eq: K -> K -> Bool, st: List<&2, P.Entry<K>>, +y: K, h: {St(~K, ~eq, st, y) == None{} : Maybe<&2, P.Status>}
) -> {P.member(~K, ~eq, P.keys(K, st), y) == False{} : Bool}:
  match st:
    case Nil{}:
      {==}
    case Con{P.Entry{+z, +v}, +t}:
      keys_none.if(~K, ~eq, eq(y, z), z, v, t, y, {==}, h, hn => keys_none(~K, ~eq, t, y, hn))

def once_step(
  ~K: Data, ~eq: K -> K -> Bool, m: Maybe<&2, P.Status>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +y: K,
  hv: View(~K, ~eq, g, stale, st, y, m), hd: {P.distinct(~K, ~eq, P.keys(K, st)) == True{} : Bool}
) -> {P.distinct(~K, ~eq, P.keys(K, P.record(K, m, st, y))) == True{} : Bool}:
  match m:
    case None{}:
      hd
    case Some{s}:
      (hn, rest) = hv
      and_not_false(P.member(~K, ~eq, P.keys(K, st), y), P.distinct(~K, ~eq, P.keys(K, st)), keys_none(~K, ~eq, st, y, hn), hd)

def once_go(
  ~K: Data, ~eq: K -> K -> Bool, p: List<&2, K>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +rs: List<&2, Bool>,
  hd: {P.distinct(~K, ~eq, P.keys(K, st)) == True{} : Bool}
) -> {P.distinct(~K, ~eq, P.keys(K, P.exec(~K, ~eq, p, g, stale, st, rs))) == True{} : Bool}:
  match p:
    case Nil{}:
      hd
    case Con{+y, t}:
      +a = P.decide(~K, ~eq, g, stale, st, y)
      once_go(~K, ~eq, t, g, stale, P.step(K, a, st, y, rs), P.step.rest(a, rs),
        once_step(~K, ~eq, P.Action.status(a, rs), g, stale, st, y, view(~K, ~eq, g, stale, st, y, rs), hd))

def Laws.exec_once(K, eq, sound, p, g, stale, rs):
  once_go(~K, ~eq, p, g, stale, Nil{}, rs, {==})

def some_keep.if(
  ~K: Data, ~eq: K -> K -> Bool, c: Bool, +y: K, +s: P.Status, +st: List<&2, P.Entry<K>>, +x: K,
  hc: {eq(x, y) == c : Bool}, h: {Maybe.is_some(&2, P.Status, St(~K, ~eq, st, x)) == True{} : Bool}
) -> {Maybe.is_some(&2, P.Status, St(~K, ~eq, P.Entry{y, s} <> st, x)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Maybe<&2, P.Status>, St(~K, ~eq, P.Entry{y, s} <> st, x), Some{s}, st_hit(~K, ~eq, y, s, st, x, hc)) :
        {Maybe.is_some(&2, P.Status, _) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, P.Status>, St(~K, ~eq, P.Entry{y, s} <> st, x), St(~K, ~eq, st, x), st_miss(~K, ~eq, y, s, st, x, hc)) :
        {Maybe.is_some(&2, P.Status, _) == True{} : Bool}
      h

def some_step(
  ~K: Data, ~eq: K -> K -> Bool, m: Maybe<&2, P.Status>, +st: List<&2, P.Entry<K>>, +y: K, +x: K,
  h: {Maybe.is_some(&2, P.Status, St(~K, ~eq, st, x)) == True{} : Bool}
) -> {Maybe.is_some(&2, P.Status, St(~K, ~eq, P.record(K, m, st, y), x)) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+s}:
      some_keep.if(~K, ~eq, eq(x, y), y, s, st, x, {==}, h)

# A status, once given, stays.
def total_keep(
  ~K: Data, ~eq: K -> K -> Bool, p: List<&2, K>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +rs: List<&2, Bool>, +x: K,
  h: {Maybe.is_some(&2, P.Status, St(~K, ~eq, st, x)) == True{} : Bool}
) -> {Maybe.is_some(&2, P.Status, St(~K, ~eq, P.exec(~K, ~eq, p, g, stale, st, rs), x)) == True{} : Bool}:
  match p:
    case Nil{}:
      h
    case Con{+y, t}:
      +a = P.decide(~K, ~eq, g, stale, st, y)
      total_keep(~K, ~eq, t, g, stale, P.step(K, a, st, y, rs), P.step.rest(a, rs), x, some_step(~K, ~eq, P.Action.status(a, rs), st, y, x, h))

def total_head(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), m: Maybe<&2, P.Status>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>,
  +st: List<&2, P.Entry<K>>, +y: K, +x: K,
  hc: {eq(x, y) == True{} : Bool}, hv: View(~K, ~eq, g, stale, st, y, m)
) -> {Maybe.is_some(&2, P.Status, St(~K, ~eq, P.record(K, m, st, y), x)) == True{} : Bool}:
  match m:
    case None{}:
      %Equal.sym(K, x, y, sound(x, y, hc)) : {Maybe.is_some(&2, P.Status, St(~K, ~eq, st, _)) == True{} : Bool}
      hv
    case Some{+s}:
      %Equal.sym(Maybe<&2, P.Status>, St(~K, ~eq, P.Entry{y, s} <> st, x), Some{s}, st_hit(~K, ~eq, y, s, st, x, hc)) :
        {Maybe.is_some(&2, P.Status, _) == True{} : Bool}
      {==}

def total_go.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +y: K, +t: List<&2, K>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>,
  +st: List<&2, P.Entry<K>>, +rs: List<&2, Bool>, +x: K,
  hc: {eq(x, y) == c : Bool}, hx: {P.member(~K, ~eq, y <> t, x) == True{} : Bool},
  ih: {P.member(~K, ~eq, t, x) == True{} : Bool} ->
    {Maybe.is_some(&2, P.Status, St(~K, ~eq, P.exec(~K, ~eq, t, g, stale, P.step(K, P.decide(~K, ~eq, g, stale, st, y), st, y, rs), P.step.rest(P.decide(~K, ~eq, g, stale, st, y), rs)), x)) == True{} : Bool}
) -> {Maybe.is_some(&2, P.Status, St(~K, ~eq, P.exec(~K, ~eq, t, g, stale, P.step(K, P.decide(~K, ~eq, g, stale, st, y), st, y, rs), P.step.rest(P.decide(~K, ~eq, g, stale, st, y), rs)), x)) == True{} : Bool}:
  match c:
    case True{}:
      +a = P.decide(~K, ~eq, g, stale, st, y)
      total_keep(~K, ~eq, t, g, stale, P.step(K, a, st, y, rs), P.step.rest(a, rs), x,
        total_head(~K, ~eq, ~sound, P.Action.status(a, rs), g, stale, st, y, x, hc, view(~K, ~eq, g, stale, st, y, rs)))
    case False{}:
      ih(mem_tail(~K, ~eq, y, t, x, hc, hx))

def total_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>,
  +st: List<&2, P.Entry<K>>, +rs: List<&2, Bool>, +x: K, hx: {P.member(~K, ~eq, p, x) == True{} : Bool}
) -> {Maybe.is_some(&2, P.Status, St(~K, ~eq, P.exec(~K, ~eq, p, g, stale, st, rs), x)) == True{} : Bool}:
  match p:
    case Nil{}:
      Empty.absurd({Maybe.is_some(&2, P.Status, St(~K, ~eq, st, x)) == True{} : Bool}, false_ne_true(hx))
    case Con{+y, +t}:
      +a = P.decide(~K, ~eq, g, stale, st, y)
      total_go.if(~K, ~eq, ~sound, eq(x, y), y, t, g, stale, st, rs, x, {==}, hx,
        hm => total_go(~K, ~eq, ~sound, t, g, stale, P.step(K, a, st, y, rs), P.step.rest(a, rs), x, hm))

def Laws.exec_total(K, eq, sound, p, g, stale, rs, x, hx):
  total_go(~K, ~eq, ~sound, p, g, stale, Nil{}, rs, x, hx)

def Inv.fresh(~K: Data, ~eq: K -> K -> Bool, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +x: K) -> Type:
  {St(~K, ~eq, st, x) == Some{P.Fresh{}} : Maybe<&2, P.Status>} -> {P.member(~K, ~eq, stale, x) == False{} : Bool}

def fresh_step.if(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), c: Bool, +stale: List<&2, K>, +st: List<&2, P.Entry<K>>, +y: K, +s: P.Status, +x: K,
  +hc: {eq(x, y) == c : Bool},
  hfr: {s == P.Fresh{} : P.Status} -> {P.member(~K, ~eq, stale, y) == False{} : Bool},
  inv: Inv.fresh(~K, ~eq, stale, st, x),
  hf: {St(~K, ~eq, P.Entry{y, s} <> st, x) == Some{P.Fresh{}} : Maybe<&2, P.Status>}
) -> {P.member(~K, ~eq, stale, x) == False{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(K, x, y, sound(x, y, hc)) : {P.member(~K, ~eq, stale, _) == False{} : Bool}
      hfr(some_inj(P.Status, s, P.Fresh{}, Equal.trans(Maybe<&2, P.Status>, Some{s}, St(~K, ~eq, P.Entry{y, s} <> st, x), Some{P.Fresh{}},
        Equal.sym(Maybe<&2, P.Status>, St(~K, ~eq, P.Entry{y, s} <> st, x), Some{s}, st_hit(~K, ~eq, y, s, st, x, hc)), hf)))
    case False{}:
      inv(Equal.trans(Maybe<&2, P.Status>, St(~K, ~eq, st, x), St(~K, ~eq, P.Entry{y, s} <> st, x), Some{P.Fresh{}},
        Equal.sym(Maybe<&2, P.Status>, St(~K, ~eq, P.Entry{y, s} <> st, x), St(~K, ~eq, st, x), st_miss(~K, ~eq, y, s, st, x, hc)), hf))

def fresh_step(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), m: Maybe<&2, P.Status>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>,
  +st: List<&2, P.Entry<K>>, +y: K, +x: K,
  hv: View(~K, ~eq, g, stale, st, y, m), inv: Inv.fresh(~K, ~eq, stale, st, x)
) -> Inv.fresh(~K, ~eq, stale, P.record(K, m, st, y), x):
  match m:
    case None{}:
      inv
    case Some{+s}:
      (hn, rest) = hv
      (hrd, hfr) = rest
      hf => fresh_step.if(~K, ~eq, ~sound, eq(x, y), stale, st, y, s, x, {==}, hfr, inv, hf)

def fresh_go(
  ~K: Data, ~eq: K -> K -> Bool, ~sound: Sound(~K, ~eq), p: List<&2, K>, +g: List<&2, P.Node<K>>, +stale: List<&2, K>,
  +st: List<&2, P.Entry<K>>, +rs: List<&2, Bool>, +x: K, inv: Inv.fresh(~K, ~eq, stale, st, x)
) -> Inv.fresh(~K, ~eq, stale, P.exec(~K, ~eq, p, g, stale, st, rs), x):
  match p:
    case Nil{}:
      inv
    case Con{+y, t}:
      +a = P.decide(~K, ~eq, g, stale, st, y)
      fresh_go(~K, ~eq, ~sound, t, g, stale, P.step(K, a, st, y, rs), P.step.rest(a, rs), x,
        fresh_step(~K, ~eq, ~sound, P.Action.status(a, rs), g, stale, st, y, x, view(~K, ~eq, g, stale, st, y, rs), inv))

def Laws.exec_fresh(K, eq, sound, p, g, stale, rs, x, hx):
  fresh_go(~K, ~eq, ~sound, p, g, stale, Nil{}, rs, x,
    h => Empty.absurd({P.member(~K, ~eq, stale, x) == False{} : Bool}, none_ne_some(P.Status, P.Fresh{}, h)))(hx)

# Fixtures
# --------

def Laws.fixture_plan():
  {==}

def Laws.fixture_plan_shared():
  {==}

def Laws.fixture_cycle():
  {==}

def Laws.fixture_missing():
  {==}

def Laws.fixture_stale():
  {==}

def Laws.fixture_reuse():
  {==}

def Laws.fixture_failure():
  {==}
