import Base
import ./LAWS.bend as Laws
import ./stats.bend as S
import bend-mathlib@0.8.0.0/nat.bend as N
import bend-mathlib@0.8.0.0/u32.bend as U
import ../lemmas/lemmas.bend as L

def Laws.sum():
  {==}

def Laws.sum_empty():
  {==}

def Laws.mean():
  {==}

def Laws.mean_empty():
  {==}

def Laws.pvariance():
  {==}

def Laws.pvariance_one():
  {==}

def Laws.variance():
  {==}

def Laws.variance_one():
  {==}

def Laws.pstdev():
  {==}

def Laws.stdev():
  {==}

def Laws.pstdev_one():
  {==}

def Laws.stdev_one():
  {==}

def Laws.pstdev_empty():
  {==}

def Laws.stdev_empty():
  {==}

def Laws.median_even():
  {==}

def Laws.median_odd():
  {==}

def Laws.median_empty():
  {==}

def Laws.quartile_low():
  {==}

def Laws.quartile_high():
  {==}

def Laws.quantile_min():
  {==}

def Laws.quantile_max():
  {==}

def Laws.percentile_90():
  {==}

def Laws.quantile_past_one():
  {==}

def Laws.quantile_zero_q():
  {==}

def Laws.quantile_big_q():
  {==}

def Laws.histogram():
  {==}

def Laws.histogram_no_bins():
  {==}

def Laws.regression_exact():
  {==}

def Laws.regression():
  {==}

def Laws.regression_flat_x():
  {==}

def Laws.regression_one():
  {==}

def Laws.regression_lengths():
  {==}

def Laws.gcd():
  {==}

def Laws.gcd_zero():
  {==}

def Laws.gcd_zero_zero():
  {==}

def Laws.gcd_fib():
  {==}

def Laws.lcm():
  {==}

def Laws.lcm_zero():
  {==}

def Laws.lcm_max():
  {==}

def Laws.lcm_overflow():
  {==}

def Laws.isqrt_zero():
  {==}

def Laws.isqrt_below():
  {==}

def Laws.isqrt_square():
  {==}

def Laws.isqrt_max():
  {==}

def min_comm(+a: U32, +b: U32) -> {U32.min(a, b) == U32.min(b, a) : U32}:
  U.u32_to_nat_inj(U32.min(a, b), U32.min(b, a),
    Equal.trans(Nat, U32.to_nat(U32.min(a, b)), Nat.min(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(U32.min(b, a)),
      U.u32_min_to_nat(a, b),
      Equal.trans(Nat, Nat.min(U32.to_nat(a), U32.to_nat(b)), Nat.min(U32.to_nat(b), U32.to_nat(a)), U32.to_nat(U32.min(b, a)),
        N.min_comm(U32.to_nat(a), U32.to_nat(b)),
        Equal.sym(Nat, U32.to_nat(U32.min(b, a)), Nat.min(U32.to_nat(b), U32.to_nat(a)), U.u32_min_to_nat(b, a)))))

def max_comm(+a: U32, +b: U32) -> {U32.max(a, b) == U32.max(b, a) : U32}:
  U.u32_to_nat_inj(U32.max(a, b), U32.max(b, a),
    Equal.trans(Nat, U32.to_nat(U32.max(a, b)), Nat.max(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(U32.max(b, a)),
      U.u32_max_to_nat(a, b),
      Equal.trans(Nat, Nat.max(U32.to_nat(a), U32.to_nat(b)), Nat.max(U32.to_nat(b), U32.to_nat(a)), U32.to_nat(U32.max(b, a)),
        N.max_comm(U32.to_nat(a), U32.to_nat(b)),
        Equal.sym(Nat, U32.to_nat(U32.max(b, a)), Nat.max(U32.to_nat(b), U32.to_nat(a)), U.u32_max_to_nat(b, a)))))

def Laws.gcd_symmetric(a, b):
  %Equal.sym(U32, U32.min(a, b), U32.min(b, a), min_comm(a, b)) :
    {S.U32.gcd.go(48n, U32.is_zero(_), U32.max(a, b), _) == S.U32.gcd(b, a) : U32}
  %Equal.sym(U32, U32.max(a, b), U32.max(b, a), max_comm(a, b)) :
    {S.U32.gcd.go(48n, U32.is_zero(U32.min(b, a)), _, U32.min(b, a)) == S.U32.gcd(b, a) : U32}
  {==}

def Laws.histogram_empty_edges():
  {==}

def Laws.histogram_nan():
  {==}

def Laws.histogram_duplicate_edges():
  {==}

def zero_test_value(+b: U32, h: {U32.is_zero(b) == True{} : Bool}) -> {U32.to_nat(b) == 0n : Nat}:
  N.eq_of_is_eq(U32.to_nat(b), 0n,
    (
      %L.u32_is_eq_nat(b, 0) : {_ == True{} : Bool}
      h
    ))

def nonzero_test_value(+b: U32, h: {U32.is_zero(b) == False{} : Bool}) -> N.lt(0n, U32.to_nat(b)):
  N.pos_of_ne_zero(U32.to_nat(b),
    (
      %L.u32_is_eq_nat(b, 0) : {_ == False{} : Bool}
      h
    ))

def divides_remainder(+d: Nat, +a: Nat, +b: Nat, +q: Nat, +r: Nat,
  hb: Laws.Divides(d, b), hr: Laws.Divides(d, r),
  e: {Nat.add(Nat.mul(q, b), r) == a : Nat}) -> Laws.Divides(d, a):
  %e : {Nat.mod(_, d) == 0n : Nat}
  %N.add_comm(r, Nat.mul(q, b)) : {Nat.mod(_, d) == 0n : Nat}
  %L.mod_add_product(r, q, b, d) : {_ == 0n : Nat}
  %Equal.sym(Nat, Nat.mod(b, d), 0n, hb) : {Nat.mod(Nat.add(r, Nat.mul(q, _)), d) == 0n : Nat}
  %N.mul_zero_sym(q) : {Nat.mod(Nat.add(r, _), d) == 0n : Nat}
  %N.add_zero_sym(r) : {Nat.mod(_, d) == 0n : Nat}
  hr

def gcd_lift(+d: U32, +a: U32, +b: U32,
  h: Laws.Divides(U32.to_nat(d), U32.to_nat(b)) & Laws.Divides(U32.to_nat(d), U32.to_nat(U32.mod(a, b))),
  qr: {Nat.add(Nat.mul(U32.to_nat(U32.div(a, b)), U32.to_nat(b)), U32.to_nat(U32.mod(a, b))) == U32.to_nat(a) : Nat} &
    N.lt(U32.to_nat(U32.mod(a, b)), U32.to_nat(b))) ->
  Laws.Divides(U32.to_nat(d), U32.to_nat(a)) & Laws.Divides(U32.to_nat(d), U32.to_nat(b)):
  (+hb, hr) = h
  (e, bound) = qr
  (divides_remainder(U32.to_nat(d), U32.to_nat(a), U32.to_nat(b), U32.to_nat(U32.div(a, b)),
    U32.to_nat(U32.mod(a, b)), hb, hr, e), hb)

def gcd_go_divides(+k: Nat, +z: Bool, +a: U32, +b: U32, hz: {z == U32.is_zero(b) : Bool}) ->
  Laws.Divides(U32.to_nat(S.U32.gcd.go(k, z, a, b)), U32.to_nat(a)) &
    Laws.Divides(U32.to_nat(S.U32.gcd.go(k, z, a, b)), U32.to_nat(b)):
  match k z:
    case 0n _:
      (N.mod_one(U32.to_nat(a)), N.mod_one(U32.to_nat(b)))
    case 1n+p True{}:
      (
        N.mod_self(U32.to_nat(a)),
        (
          %Equal.sym(Nat, U32.to_nat(b), 0n,
            zero_test_value(b, Equal.sym(Bool, True{}, U32.is_zero(b), hz))) :
            {Nat.mod(_, U32.to_nat(a)) == 0n : Nat}
          N.zero_mod(U32.to_nat(a))
        )
      )
    case 1n+p False{}:
      gcd_lift(S.U32.gcd.go(p, U32.is_zero(U32.mod(a, b)), b, U32.mod(a, b)), a, b,
        gcd_go_divides(p, U32.is_zero(U32.mod(a, b)), b, U32.mod(a, b), {==}),
        L.u32_divmod_nat(a, b, nonzero_test_value(b, Equal.sym(Bool, False{}, U32.is_zero(b), hz))))

def gcd_ordered_pick(t: Bool, +a: U32, +b: U32, +d: Nat,
  h: Laws.Divides(d, U32.to_nat(Bool.pick(U32, t, b, a))) &
    Laws.Divides(d, U32.to_nat(Bool.pick(U32, t, a, b)))) ->
  Laws.Divides(d, U32.to_nat(a)) & Laws.Divides(d, U32.to_nat(b)):
  match t:
    case True{}:
      (hb, ha) = h
      (ha, hb)
    case False{}:
      h

def gcd_ordered(+a: U32, +b: U32, h: Laws.Divides(U32.to_nat(S.U32.gcd(a, b)), U32.to_nat(U32.max(a, b))) &
  Laws.Divides(U32.to_nat(S.U32.gcd(a, b)), U32.to_nat(U32.min(a, b)))) ->
  Laws.Divides(U32.to_nat(S.U32.gcd(a, b)), U32.to_nat(a)) &
    Laws.Divides(U32.to_nat(S.U32.gcd(a, b)), U32.to_nat(b)):
  match a b:
    case U32{+x} U32{+y}:
      gcd_ordered_pick(U32.is_lt(U32{x}, U32{y}), U32{x}, U32{y}, U32.to_nat(S.U32.gcd(U32{x}, U32{y})), h)

def Laws.gcd_divides(a, b):
  gcd_ordered(a, b, gcd_go_divides(48n, U32.is_zero(U32.min(a, b)), U32.max(a, b), U32.min(a, b), {==}))

def divides_quotient(+d: Nat, +a: Nat, h: Laws.Divides(d, a)) -> {Nat.mul(Nat.div(a, d), d) == a : Nat}:
  %N.add_zero(Nat.mul(Nat.div(a, d), d)) : {_ == a : Nat}
  %h : {Nat.add(Nat.mul(Nat.div(a, d), d), _) == a : Nat}
  %N.mul_comm(d, Nat.div(a, d)) : {Nat.add(_, Nat.mod(a, d)) == a : Nat}
  N.div_add_mod(a, d)

def quotient_exact(z: Bool, +a: U32, +g: U32, hz: {z == U32.is_zero(g) : Bool},
  h: Laws.Divides(U32.to_nat(g), U32.to_nat(a))) ->
  {Nat.mul(U32.to_nat(U32.div(a, g)), U32.to_nat(g)) == U32.to_nat(a) : Nat}:
  match z:
    case True{}:
      +eg = zero_test_value(g, Equal.sym(Bool, True{}, U32.is_zero(g), hz))
      +ea : {U32.to_nat(a) == 0n : Nat} = (
        %eg : {Nat.mod(U32.to_nat(a), _) == 0n : Nat}
        h
      )
      %Equal.sym(Nat, U32.to_nat(g), 0n, eg) : {Nat.mul(U32.to_nat(U32.div(a, g)), _) == U32.to_nat(a) : Nat}
      Equal.trans(Nat, Nat.mul(U32.to_nat(U32.div(a, g)), 0n), 0n, U32.to_nat(a),
        N.mul_zero(U32.to_nat(U32.div(a, g))), Equal.sym(Nat, U32.to_nat(a), 0n, ea))
    case False{}:
      %Equal.sym(Nat, U32.to_nat(U32.div(a, g)), Nat.div(U32.to_nat(a), U32.to_nat(g)),
        L.u32_div_nat(a, g, nonzero_test_value(g, Equal.sym(Bool, False{}, U32.is_zero(g), hz)))) :
        {Nat.mul(_, U32.to_nat(g)) == U32.to_nat(a) : Nat}
      divides_quotient(U32.to_nat(g), U32.to_nat(a), h)

def lcm_left(+q: Nat, +g: Nat, +a: Nat, +b: Nat,
  eq: {Nat.mul(q, g) == a : Nat}, hb: Laws.Divides(g, b)) -> Laws.Divides(a, Nat.mul(q, b)):
  %divides_quotient(g, b, hb) : {Nat.mod(Nat.mul(q, _), a) == 0n : Nat}
  %N.mul_comm(g, Nat.div(b, g)) : {Nat.mod(Nat.mul(q, _), a) == 0n : Nat}
  %N.mul_assoc(q, g, Nat.div(b, g)) : {Nat.mod(_, a) == 0n : Nat}
  %Equal.sym(Nat, Nat.mul(q, g), a, eq) : {Nat.mod(Nat.mul(_, Nat.div(b, g)), a) == 0n : Nat}
  N.mul_mod_right(a, Nat.div(b, g))

def lcm_product(+q: U32, +g: U32, +a: U32, +b: U32,
  hq: {Nat.mul(U32.to_nat(q), U32.to_nat(g)) == U32.to_nat(a) : Nat},
  hb: Laws.Divides(U32.to_nat(g), U32.to_nat(b)),
  bound: N.lt(Nat.mul(U32.to_nat(q), U32.to_nat(b)), L.pow2(32n))) ->
  Laws.CommonMultiple(a, b, Some{U32.mul(q, b)}):
  %Equal.sym(Nat, U32.to_nat(U32.mul(q, b)), Nat.mul(U32.to_nat(q), U32.to_nat(b)), L.u32_mul_nat(q, b, bound)) :
    Laws.Divides(U32.to_nat(a), _) & Laws.Divides(U32.to_nat(b), _)
  (lcm_left(U32.to_nat(q), U32.to_nat(g), U32.to_nat(a), U32.to_nat(b), hq, hb),
    N.mul_mod_left(U32.to_nat(q), U32.to_nat(b)))

def u32_gt_lt(+a: U32, +b: U32) -> {U32.is_gt(a, b) == Nat.is_lt(U32.to_nat(b), U32.to_nat(a)) : Bool}:
  Equal.trans(Bool, U32.is_gt(a, b), Nat.is_gt(U32.to_nat(a), U32.to_nat(b)),
    Nat.is_lt(U32.to_nat(b), U32.to_nat(a)), U.u32_is_gt_to_nat(a, b), N.is_gt_eq_is_lt(U32.to_nat(a), U32.to_nat(b)))

def lcm_bound(+q: U32, +b: U32, +hb: N.lt(0n, U32.to_nat(b)),
  hq: {U32.is_gt(q, U32.div(4294967295, b)) == False{} : Bool}) ->
  N.lt(Nat.mul(U32.to_nat(q), U32.to_nat(b)), L.pow2(32n)):
  +h : N.le(U32.to_nat(q), U32.to_nat(U32.div(4294967295, b))) =
    N.le_of_not_lt(U32.to_nat(U32.div(4294967295, b)), U32.to_nat(q),
      (
        %u32_gt_lt(q, U32.div(4294967295, b)) : {_ == False{} : Bool}
        hq
      ))
  N.lt_of_le_of_lt(Nat.mul(U32.to_nat(q), U32.to_nat(b)), U32.to_nat(4294967295), L.pow2(32n),
    N.le_trans(Nat.mul(U32.to_nat(q), U32.to_nat(b)),
      Nat.mul(Nat.div(U32.to_nat(4294967295), U32.to_nat(b)), U32.to_nat(b)), U32.to_nat(4294967295),
      (
        %L.u32_div_nat(4294967295, b, hb) :
          N.le(Nat.mul(U32.to_nat(q), U32.to_nat(b)), Nat.mul(_, U32.to_nat(b)))
        N.mul_le_mul_right(U32.to_nat(q), U32.to_nat(U32.div(4294967295, b)), U32.to_nat(b), h)
      ),
      N.div_mul_le_self(U32.to_nat(4294967295), U32.to_nat(b))),
    L.u32_to_nat_lt(4294967295))

def lcm_guard(z: Bool, ov: Bool, +q: U32, +g: U32, +a: U32, +b: U32,
  hz: {z == U32.is_zero(b) : Bool},
  hov: {ov == Bool.and(Bool.not(z), U32.is_gt(q, U32.div(4294967295, b))) : Bool},
  hq: {Nat.mul(U32.to_nat(q), U32.to_nat(g)) == U32.to_nat(a) : Nat},
  hb: Laws.Divides(U32.to_nat(g), U32.to_nat(b))) ->
  Laws.CommonMultiple(a, b, S.U32.lcm.if(ov, q, b)):
  match z ov:
    case True{} True{}:
      Empty.absurd(Unit, N.succ_ne_zero(0n)(Equal.cong(Bool, Nat, L.b2n, True{}, False{}, hov)))
    case True{} False{}:
      +eb = zero_test_value(b, Equal.sym(Bool, True{}, U32.is_zero(b), hz))
      lcm_product(q, g, a, b, hq, hb,
        (
          %Equal.sym(Nat, U32.to_nat(b), 0n, eb) : N.lt(Nat.mul(U32.to_nat(q), _), L.pow2(32n))
          %N.mul_zero_sym(U32.to_nat(q)) : N.lt(_, L.pow2(32n))
          L.lt_rw(0n, U32.to_nat(0), L.pow2(32n), {==}, L.u32_to_nat_lt(0))
        ))
    case False{} True{}:
      Unit{}
    case False{} False{}:
      lcm_product(q, g, a, b, hq, hb,
        lcm_bound(q, b, nonzero_test_value(b, Equal.sym(Bool, False{}, U32.is_zero(b), hz)),
          Equal.sym(Bool, False{}, U32.is_gt(q, U32.div(4294967295, b)), hov)))

def lcm_of(+a: U32, +b: U32, h: Laws.Divides(U32.to_nat(S.U32.gcd(a, b)), U32.to_nat(a)) &
  Laws.Divides(U32.to_nat(S.U32.gcd(a, b)), U32.to_nat(b))) -> Laws.CommonMultiple(a, b, S.U32.lcm(a, b)):
  (ha, hb) = h
  lcm_guard(U32.is_zero(b),
    Bool.and(Bool.not(U32.is_zero(b)), U32.is_gt(U32.div(a, S.U32.gcd(a, b)), U32.div(4294967295, b))),
    U32.div(a, S.U32.gcd(a, b)), S.U32.gcd(a, b), a, b, {==}, {==},
    quotient_exact(U32.is_zero(S.U32.gcd(a, b)), a, S.U32.gcd(a, b), {==}, ha), hb)

def Laws.lcm_divisible(a, b):
  lcm_of(a, b, Laws.gcd_divides(a, b))

def pow2_mul(+a: Nat, +b: Nat) -> {Nat.mul(L.pow2(a), L.pow2(b)) == L.pow2(Nat.add(a, b)) : Nat}:
  match a:
    case 0n:
      N.one_mul(L.pow2(b))
    case 1n+p:
      %N.double_mul(L.pow2(p), L.pow2(b)) : {_ == L.pow2(Nat.add(1n+p, b)) : Nat}
      Equal.cong(Nat, Nat, Nat.double, Nat.mul(L.pow2(p), L.pow2(b)), L.pow2(Nat.add(p, b)), pow2_mul(p, b))

def pow2_lt_step(+p: Nat) -> N.lt(L.pow2(p), L.pow2(1n+p)):
  match p:
    case 0n:
      {==}
    case 1n+q:
      N.double_lt_double(L.pow2(q), L.pow2(1n+q), pow2_lt_step(q))

def pow2_le_add(+m: Nat, +n: Nat) -> N.le(L.pow2(n), L.pow2(Nat.add(m, n))):
  match m:
    case 0n:
      N.le_refl(L.pow2(n))
    case 1n+p:
      N.le_trans(L.pow2(n), L.pow2(Nat.add(p, n)), L.pow2(1n+Nat.add(p, n)),
        pow2_le_add(p, n), N.le_double(L.pow2(Nat.add(p, n))))

def halve_pow2(+p: Nat) -> {Nat.div(L.pow2(1n+p), 2n) == L.pow2(p) : Nat}:
  %N.double_eq_two_mul_sym(L.pow2(p)) : {Nat.div(_, 2n) == L.pow2(p) : Nat}
  N.mul_div_cancel_left(L.pow2(p), 1n)

def Frame(+k: Nat, +n: Nat, +r: Nat, +limit: Nat) -> Type:
  N.le(Nat.mul(r, r), n) &
    (N.lt(n, Nat.mul(Nat.add(r, L.pow2(k)), Nat.add(r, L.pow2(k)))) &
      N.le(Nat.add(r, L.pow2(k)), limit))

def candidate_next(+p: Nat, +r: Nat, +c: Nat, ec: {c == Nat.add(r, L.pow2(p)) : Nat}) ->
  {Nat.add(c, L.pow2(p)) == Nat.add(r, L.pow2(1n+p)) : Nat}:
  %Equal.sym(Nat, c, Nat.add(r, L.pow2(p)), ec) : {Nat.add(_, L.pow2(p)) == Nat.add(r, L.pow2(1n+p)) : Nat}
  %N.double_eq_add_sym(L.pow2(p)) : {Nat.add(Nat.add(r, L.pow2(p)), L.pow2(p)) == Nat.add(r, _) : Nat}
  N.add_assoc(r, L.pow2(p), L.pow2(p))

def candidate_lt(+p: Nat, +n: Nat, +r: Nat, +limit: Nat, h: Frame(1n+p, n, r, limit)) ->
  N.lt(Nat.add(r, L.pow2(p)), limit):
  (lo, interval) = h
  (hi, cap) = interval
  N.lt_of_lt_of_le(Nat.add(r, L.pow2(p)), Nat.add(r, L.pow2(1n+p)), limit,
    N.add_lt_add_left(L.pow2(p), L.pow2(1n+p), r, pow2_lt_step(p)), cap)

def frame_taken(+p: Nat, +n: Nat, +r: Nat, +c: Nat, +limit: Nat,
  ec: {c == Nat.add(r, L.pow2(p)) : Nat}, lo: N.le(Nat.mul(c, c), n), h: Frame(1n+p, n, r, limit)) ->
  Frame(p, n, c, limit):
  (old_lo, interval) = h
  (
    lo,
    (
      %Equal.sym(Nat, Nat.add(c, L.pow2(p)), Nat.add(r, L.pow2(1n+p)), candidate_next(p, r, c, ec)) :
        N.lt(n, Nat.mul(_, _)) & N.le(_, limit)
      interval
    )
  )

def frame_rejected(+p: Nat, +n: Nat, +r: Nat, +c: Nat, +limit: Nat,
  ec: {c == Nat.add(r, L.pow2(p)) : Nat}, hi: N.lt(n, Nat.mul(c, c)), h: Frame(1n+p, n, r, limit)) ->
  Frame(p, n, r, limit):
  (lo, interval) = h
  (old_hi, cap) = interval
  (
    lo,
    (
      (
        %ec : N.lt(n, Nat.mul(_, _))
        hi
      ),
      N.le_trans(Nat.add(r, L.pow2(p)), Nat.add(r, L.pow2(1n+p)), limit,
        N.add_le_add_left(L.pow2(p), L.pow2(1n+p), r, N.le_double(L.pow2(p))), cap)
    )
  )

def frame_pick(ok: Bool, +p: Nat, +n: Nat, +r: Nat, +c: Nat, +limit: Nat,
  ec: {c == Nat.add(r, L.pow2(p)) : Nat},
  test: {Nat.is_le(Nat.mul(c, c), n) == ok : Bool}, h: Frame(1n+p, n, r, limit)) ->
  Frame(p, n, Bool.pick(Nat, ok, c, r), limit):
  match ok:
    case True{}:
      frame_taken(p, n, r, c, limit, ec, test, h)
    case False{}:
      frame_rejected(p, n, r, c, limit, ec, N.lt_of_not_le(Nat.mul(c, c), n, test), h)

def half_word(+p: Nat, +step: U32, hstep: {U32.to_nat(step) == L.pow2(1n+p) : Nat}) ->
  {U32.to_nat(U32.div(step, 2)) == L.pow2(p) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.div(step, 2)), Nat.div(U32.to_nat(step), 2n), L.pow2(p),
    L.u32_div_nat(step, 2, {==}),
    (
      %Equal.sym(Nat, U32.to_nat(step), L.pow2(1n+p), hstep) :
        {Nat.div(_, 2n) == L.pow2(p) : Nat}
      halve_pow2(p)
    ))

def candidate_word(+p: Nat, +n: Nat, +r: U32, +half: U32, +limit: Nat,
  hhalf: {U32.to_nat(half) == L.pow2(p) : Nat}, h: Frame(1n+p, n, U32.to_nat(r), limit),
  hlimit: N.le(limit, L.pow2(32n))) ->
  {U32.to_nat(U32.add(r, half)) == Nat.add(U32.to_nat(r), L.pow2(p)) : Nat}:
  +e = Equal.cong(Nat, Nat, v => Nat.add(U32.to_nat(r), v), U32.to_nat(half), L.pow2(p), hhalf)
  Equal.trans(Nat, U32.to_nat(U32.add(r, half)), Nat.add(U32.to_nat(r), U32.to_nat(half)),
    Nat.add(U32.to_nat(r), L.pow2(p)),
    L.u32_add_nat(r, half,
      L.lt_rw(Nat.add(U32.to_nat(r), U32.to_nat(half)), Nat.add(U32.to_nat(r), L.pow2(p)), L.pow2(32n), e,
        N.lt_of_lt_of_le(Nat.add(U32.to_nat(r), L.pow2(p)), limit, L.pow2(32n),
          candidate_lt(p, n, U32.to_nat(r), limit, h), hlimit))), e)

def square_word(+c: U32, +limit: Nat, hlimit: {Nat.mul(limit, limit) == L.pow2(32n) : Nat},
  +hc: N.lt(U32.to_nat(c), limit)) ->
  {U32.to_nat(U32.mul(c, c)) == Nat.mul(U32.to_nat(c), U32.to_nat(c)) : Nat}:
  L.u32_mul_nat(c, c,
    (
      %hlimit : N.lt(Nat.mul(U32.to_nat(c), U32.to_nat(c)), _)
      N.mul_lt_mul_of_lt_of_lt(U32.to_nat(c), U32.to_nat(c), limit, limit, hc, hc)
    ))

def square_test(+c: U32, +n: U32,
  es: {U32.to_nat(U32.mul(c, c)) == Nat.mul(U32.to_nat(c), U32.to_nat(c)) : Nat}) ->
  {U32.is_le(U32.mul(c, c), n) == Nat.is_le(Nat.mul(U32.to_nat(c), U32.to_nat(c)), U32.to_nat(n)) : Bool}:
  Equal.trans(Bool, U32.is_le(U32.mul(c, c), n), Nat.is_le(U32.to_nat(U32.mul(c, c)), U32.to_nat(n)),
    Nat.is_le(Nat.mul(U32.to_nat(c), U32.to_nat(c)), U32.to_nat(n)), L.u32_is_le_nat(U32.mul(c, c), n),
    Equal.cong(Nat, Bool, v => Nat.is_le(v, U32.to_nat(n)), U32.to_nat(U32.mul(c, c)),
      Nat.mul(U32.to_nat(c), U32.to_nat(c)), es))

def pick_nat(ok: Bool, +c: U32, +r: U32) ->
  {U32.to_nat(S.U32.isqrt.pick(ok, c, r)) == Bool.pick(Nat, ok, U32.to_nat(c), U32.to_nat(r)) : Nat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def frame_pick_word(+ok: Bool, +p: Nat, +n: U32, +r: U32, +c: U32, +limit: Nat,
  ec: {U32.to_nat(c) == Nat.add(U32.to_nat(r), L.pow2(p)) : Nat},
  test: {Nat.is_le(Nat.mul(U32.to_nat(c), U32.to_nat(c)), U32.to_nat(n)) == ok : Bool},
  h: Frame(1n+p, U32.to_nat(n), U32.to_nat(r), limit)) ->
  Frame(p, U32.to_nat(n), U32.to_nat(S.U32.isqrt.pick(ok, c, r)), limit):
  %Equal.sym(Nat, U32.to_nat(S.U32.isqrt.pick(ok, c, r)), Bool.pick(Nat, ok, U32.to_nat(c), U32.to_nat(r)),
    pick_nat(ok, c, r)) : Frame(p, U32.to_nat(n), _, limit)
  frame_pick(ok, p, U32.to_nat(n), U32.to_nat(r), U32.to_nat(c), limit, ec, test, h)

def frame_done(+n: Nat, +r: Nat, +limit: Nat, h: Frame(0n, n, r, limit)) -> Laws.SqrtBounds(n, r):
  (lo, interval) = h
  (hi, cap) = interval
  (
    lo,
    (
      %N.add_comm(r, 1n) : N.lt(n, Nat.mul(_, _))
      hi
    )
  )

def sqrt_frame(+p: Nat, +n: U32, +r: U32, +step: U32, +limit: Nat,
  hlimit: {Nat.mul(limit, limit) == L.pow2(32n) : Nat}, hlelimit: N.le(limit, L.pow2(32n)),
  hstep: {U32.to_nat(step) == L.pow2(1n+p) : Nat}, h: Frame(1n+p, U32.to_nat(n), U32.to_nat(r), limit)) ->
  Frame(p, U32.to_nat(n), U32.to_nat(S.U32.isqrt.pick(
    U32.is_le(U32.mul(U32.add(r, U32.div(step, 2)), U32.add(r, U32.div(step, 2))), n),
    U32.add(r, U32.div(step, 2)), r)), limit):
  (+lo, interval) = h
  (+hi, cap) = interval
  +cap : N.le(Nat.add(U32.to_nat(r), L.pow2(1n+p)), limit) = cap
  +half = U32.div(step, 2)
  +c = U32.add(r, half)
  +eh = half_word(p, step, hstep)
  +ec = candidate_word(p, U32.to_nat(n), r, half, limit, eh, (lo, (hi, cap)), hlelimit)
  +hc = L.lt_rw(U32.to_nat(c), Nat.add(U32.to_nat(r), L.pow2(p)), limit, ec,
    candidate_lt(p, U32.to_nat(n), U32.to_nat(r), limit, (lo, (hi, cap))))
  +es = square_word(c, limit, hlimit, hc)
  frame_pick_word(U32.is_le(U32.mul(c, c), n), p, n, r, c, limit, ec,
    Equal.sym(Bool, U32.is_le(U32.mul(c, c), n), Nat.is_le(Nat.mul(U32.to_nat(c), U32.to_nat(c)), U32.to_nat(n)),
      square_test(c, n, es)), (lo, (hi, cap)))

def sqrt_go(+k: Nat, +n: U32, +r: U32, +step: U32, +limit: Nat,
  +hlimit: {Nat.mul(limit, limit) == L.pow2(32n) : Nat}, +hlelimit: N.le(limit, L.pow2(32n)),
  +hstep: {U32.to_nat(step) == L.pow2(k) : Nat}, h: Frame(k, U32.to_nat(n), U32.to_nat(r), limit)) ->
  Laws.SqrtBounds(U32.to_nat(n), U32.to_nat(S.U32.isqrt.go(k, n, r, step))):
  match k:
    case 0n:
      frame_done(U32.to_nat(n), U32.to_nat(r), limit, h)
    case 1n+p:
      +half = U32.div(step, 2)
      +c = U32.add(r, half)
      sqrt_go(p, n, S.U32.isqrt.pick(U32.is_le(U32.mul(c, c), n), c, r), half, limit, hlimit, hlelimit,
        half_word(p, step, hstep), sqrt_frame(p, n, r, step, limit, hlimit, hlelimit, hstep, h))

def power_word(+n: Nat, +p: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+np:
      match p:
        case 0n:
          WCon{True{}, Word.zero(np)}
        case 1n+pp:
          WCon{False{}, power_word(np, pp)}

def power_word_nat(+n: Nat, +p: Nat, h: N.lt(p, n)) ->
  {Word.to_nat(n, power_word(n, p)) == L.pow2(p) : Nat}:
  match n:
    case 0n:
      Empty.absurd({Word.to_nat(0n, power_word(0n, p)) == L.pow2(p) : Nat}, N.lt_zero(p)(h))
    case 1n+np:
      match p:
        case 0n:
          Equal.cong(Nat, Nat, v => 1n+Nat.double(v), Word.to_nat(np, Word.zero(np)), 0n, L.word_zero_nat(np))
        case 1n+pp:
          Equal.cong(Nat, Nat, Nat.double, Word.to_nat(np, power_word(np, pp)),
            L.pow2(pp), power_word_nat(np, pp, h))

def power_word_literal() -> {U32{power_word(32n, 16n)} == 65536 : U32}:
  {==}

def initial_step() -> {U32.to_nat(65536) == L.pow2(16n) : Nat}:
  Equal.trans(Nat, U32.to_nat(65536), Word.to_nat(32n, power_word(32n, 16n)), L.pow2(16n),
    Equal.sym(Nat, Word.to_nat(32n, power_word(32n, 16n)), U32.to_nat(65536),
      Equal.trans(Nat, Word.to_nat(32n, power_word(32n, 16n)), U32.to_nat(U32{power_word(32n, 16n)}), U32.to_nat(65536),
        L.u32_to_nat_word(power_word(32n, 16n)),
        Equal.cong(U32, Nat, U32.to_nat, U32{power_word(32n, 16n)}, 65536, power_word_literal()))),
    power_word_nat(32n, 16n, {==}))

def initial_frame(+p: Nat, +n: U32, +r: U32, +limit: Nat, +e: {limit == L.pow2(p) : Nat},
  square: {Nat.mul(limit, limit) == L.pow2(32n) : Nat}, er: {U32.to_nat(r) == 0n : Nat}) ->
  Frame(p, U32.to_nat(n), U32.to_nat(r), limit):
  %Equal.sym(Nat, U32.to_nat(r), 0n, er) : Frame(p, U32.to_nat(n), _, limit)
  (
    N.zero_le(U32.to_nat(n)),
    (
      (
        %e : N.lt(U32.to_nat(n), Nat.mul(_, _))
        %Equal.sym(Nat, Nat.mul(limit, limit), L.pow2(32n), square) : N.lt(U32.to_nat(n), _)
        L.u32_to_nat_lt(n)
      ),
      (
        %e : N.le(_, limit)
        N.le_refl(limit)
      )
    )
  )

def square_limit() -> {Nat.mul(L.pow2(16n), L.pow2(16n)) == L.pow2(32n) : Nat}:
  Equal.trans(Nat, Nat.mul(L.pow2(16n), L.pow2(16n)), L.pow2(Nat.add(16n, 16n)), L.pow2(32n),
    pow2_mul(16n, 16n), Equal.cong(Nat, Nat, L.pow2, Nat.add(16n, 16n), 32n, {==}))

def le_limit() -> N.le(L.pow2(16n), L.pow2(32n)):
  %Equal.cong(Nat, Nat, L.pow2, Nat.add(16n, 16n), 32n, {==}) : N.le(L.pow2(16n), _)
  pow2_le_add(16n, 16n)

def Laws.isqrt_bounds(n):
  sqrt_go(16n, n, 0, 65536, L.pow2(16n), square_limit(), le_limit(),
    initial_step(), initial_frame(16n, n, 0, L.pow2(16n), {==}, square_limit(), {==}))
