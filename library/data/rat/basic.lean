/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.rat.basic
Author: Jeremy Avigad

The rational numbers as a field generated by the integers, defined as the usual quotient.
-/
import data.int algebra.field
open int quot eq.ops

record prerat : Type :=
(num : ℤ) (denom : ℤ) (denom_pos : denom > 0)

/-
  prerat: the representations of the rationals as integers num, denom, with denom > 0.
  note: names are not protected, because it is not expected that users will open prerat.
-/

namespace prerat

/- the equivalence relation -/

definition equiv (a b : prerat) : Prop := num a * denom b = num b * denom a

infix `≡` := equiv

theorem equiv.refl [refl] (a : prerat) : a ≡ a := rfl

theorem equiv.symm [symm] {a b : prerat} (H : a ≡ b) : b ≡ a := !eq.symm H

theorem num_eq_zero_of_equiv {a b : prerat} (H : a ≡ b) (na_zero : num a = 0) : num b = 0 :=
have H1 : num a * denom b = 0, from !zero_mul ▸ na_zero ▸ rfl,
have H2 : num b * denom a = 0, from H ▸ H1,
show num b = 0, from or_resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero H2) (ne_of_gt (denom_pos a))

theorem num_pos_of_equiv {a b : prerat} (H : a ≡ b) (na_pos : num a > 0) : num b > 0 :=
have H1 : num a * denom b > 0, from mul_pos na_pos (denom_pos b),
have H2 : num b * denom a > 0, from H ▸ H1,
show num b > 0, from pos_of_mul_pos_right H2 (le_of_lt (denom_pos a))

theorem num_neg_of_equiv {a b : prerat} (H : a ≡ b) (na_neg : num a < 0) : num b < 0 :=
have H1 : num a * denom b < 0, from mul_neg_of_neg_of_pos na_neg (denom_pos b),
have H2 : -(-num b * denom a) < 0, from !neg_mul_eq_neg_mul⁻¹ ▸ !neg_neg⁻¹ ▸ H ▸ H1,
have H3 : -num b > 0, from pos_of_mul_pos_right (pos_of_neg_neg H2) (le_of_lt (denom_pos a)),
neg_of_neg_pos H3

theorem equiv_of_num_eq_zero {a b : prerat} (H1 : num a = 0) (H2 : num b = 0) : a ≡ b :=
by rewrite [↑equiv, H1, H2, *zero_mul]

theorem equiv.trans [trans] {a b c : prerat} (H1 : a ≡ b) (H2 : b ≡ c) : a ≡ c :=
decidable.by_cases
  (assume b0 : num b = 0,
    have a0 : num a = 0, from num_eq_zero_of_equiv (equiv.symm H1) b0,
    have c0 : num c = 0, from num_eq_zero_of_equiv H2 b0,
    equiv_of_num_eq_zero a0 c0)
  (assume bn0 : num b ≠ 0,
    have H3 : num b * denom b ≠ 0, from mul_ne_zero bn0 (ne_of_gt (denom_pos b)),
    have H4 : (num b * denom b) * (num a * denom c) = (num b * denom b) * (num c * denom a),
      from calc
        (num b * denom b) * (num a * denom c) = (num a * denom b) * (num b * denom c) :
                    by rewrite [*mul.assoc, *mul.left_comm (num a), *mul.left_comm (num b)]
          ... = (num b * denom a) * (num b * denom c)                                 : {H1}
          ... = (num b * denom a) * (num c * denom b)                                 : {H2}
          ... = (num b * denom b) * (num c * denom a)                                 :
                    by rewrite [*mul.assoc, *mul.left_comm (denom a),
                                   *mul.left_comm (denom b), mul.comm (denom a)],
    mul.cancel_left H3 H4)

theorem equiv.is_equivalence : equivalence equiv :=
  mk_equivalence equiv equiv.refl @equiv.symm @equiv.trans

definition setoid : setoid prerat :=
setoid.mk equiv equiv.is_equivalence

/- field operations -/

private theorem of_nat_succ_pos (n : nat) : of_nat (nat.succ n) > 0 :=
of_nat_pos !nat.succ_pos

definition of_int (i : int) : prerat := prerat.mk i 1 !of_nat_succ_pos

definition zero : prerat := of_int 0

definition one : prerat := of_int 1

private theorem mul_denom_pos (a b : prerat) : denom a * denom b > 0 :=
mul_pos (denom_pos a) (denom_pos b)

definition add (a b : prerat) : prerat :=
prerat.mk (num a * denom b + num b * denom a) (denom a * denom b) (mul_denom_pos a b)

definition mul (a b : prerat) : prerat :=
prerat.mk (num a * num b) (denom a * denom b) (mul_denom_pos a b)

definition neg (a : prerat) : prerat :=
prerat.mk (- num a) (denom a) (denom_pos a)

definition inv : prerat → prerat
| inv (prerat.mk nat.zero d dp) := zero
| inv (prerat.mk (nat.succ n) d dp) := prerat.mk d (nat.succ n) !of_nat_succ_pos
| inv (prerat.mk -[n +1] d dp) := prerat.mk (-d) (nat.succ n) !of_nat_succ_pos

theorem equiv_zero_of_num_eq_zero {a : prerat} (H : num a = 0) : a ≡ zero :=
by rewrite [↑equiv, H, ↑zero, ↑num, ↑of_int, *zero_mul]

theorem num_eq_zero_of_equiv_zero {a : prerat} : a ≡ zero → num a = 0 :=
by rewrite [↑equiv, ↑zero, ↑of_int, mul_one, zero_mul]; intro H; exact H

theorem inv_zero {d : int} (dp : d > 0) : inv (mk nat.zero d dp) = zero :=
begin rewrite [↑inv, ▸*] end

theorem inv_zero' : inv zero = zero := inv_zero (of_nat_succ_pos nat.zero)

theorem inv_of_pos {n d : int} (np : n > 0) (dp : d > 0) : inv (mk n d dp) ≡ mk d n np :=
obtain (n' : nat) (Hn' : n = of_nat n'), from exists_eq_of_nat (le_of_lt np),
have H1 : (#nat n' > nat.zero), from lt_of_of_nat_lt_of_nat (Hn' ▸ np),
obtain (k : nat) (Hk : n' = nat.succ k), from nat.exists_eq_succ_of_lt H1,
have H2 : d * n = d * nat.succ k, by rewrite [Hn', Hk],
Hn'⁻¹ ▸ (Hk⁻¹ ▸ H2)

theorem inv_neg {n d : int} (np : n > 0) (dp : d > 0) : inv (mk (-n) d dp) ≡ mk (-d) n np :=
obtain (n' : nat) (Hn' : n = of_nat n'), from exists_eq_of_nat (le_of_lt np),
have H1 : (#nat n' > nat.zero), from lt_of_of_nat_lt_of_nat (Hn' ▸ np),
obtain (k : nat) (Hk : n' = nat.succ k), from nat.exists_eq_succ_of_lt H1,
have H2 : -d * n = -d * nat.succ k, by rewrite [Hn', Hk],
have H3 : inv (mk -[k +1] d dp) ≡ mk (-d) n np, from H2,
have H4 : -[k +1] = -n, from calc
  -[k +1] = -(nat.succ k) : rfl
      ... = -n            : by rewrite [Hk⁻¹, Hn'],
H4 ▸ H3

theorem inv_of_neg {n d : int} (nn : n < 0) (dp : d > 0) :
  inv (mk n d dp) ≡ mk (-d) (-n) (neg_pos_of_neg nn) :=
have H : inv (mk (-(-n)) d dp) ≡ mk (-d) (-n) (neg_pos_of_neg nn),
  from inv_neg (neg_pos_of_neg nn) dp,
!neg_neg ▸ H

/- operations respect equiv -/

theorem add_equiv_add {a1 b1 a2 b2 : prerat} (eqv1 : a1 ≡ a2) (eqv2 : b1 ≡ b2) :
  add a1 b1 ≡ add a2 b2 :=
calc
  (num a1 * denom b1 + num b1 * denom a1) * (denom a2 * denom b2)
      = num a1 * denom a2 * denom b1 * denom b2 + num b1 * denom b2 * denom a1 * denom a2 :
          by rewrite [mul.right_distrib, *mul.assoc, mul.left_comm (denom b1),
                      mul.comm (denom b2), *mul.assoc]
  ... = num a2 * denom a1 * denom b1 * denom b2 + num b2 * denom b1 * denom a1 * denom a2 :
          by rewrite [↑equiv at *, eqv1, eqv2]
  ... = (num a2 * denom b2 + num b2 * denom a2) * (denom a1 * denom b1) :
          by rewrite [mul.right_distrib, *mul.assoc, *mul.left_comm (denom b2),
                      *mul.comm (denom b1), *mul.assoc, mul.left_comm (denom a2)]

theorem mul_equiv_mul {a1 b1 a2 b2 : prerat} (eqv1 : a1 ≡ a2) (eqv2 : b1 ≡ b2) :
  mul a1 b1 ≡ mul a2 b2 :=
calc
  (num a1 * num b1) * (denom a2 * denom b2)
      = (num a1 * denom a2) * (num b1 * denom b2) : by rewrite [*mul.assoc, mul.left_comm (num b1)]
  ... = (num a2 * denom a1) * (num b2 * denom b1) : by rewrite [↑equiv at *, eqv1, eqv2]
  ... = (num a2 * num b2) * (denom a1 * denom b1) : by rewrite [*mul.assoc, mul.left_comm (num b2)]

theorem neg_equiv_neg {a b : prerat} (eqv : a ≡ b) : neg a ≡ neg b :=
calc
  -num a * denom b = -(num a * denom b) : neg_mul_eq_neg_mul
               ... = -(num b * denom a) : {eqv}
               ... = -num b * denom a   : neg_mul_eq_neg_mul

theorem inv_equiv_inv : ∀{a b : prerat}, a ≡ b → inv a ≡ inv b
| (mk an ad adp) (mk bn bd bdp) :=
  assume H,
  lt.by_cases
    (assume an_neg : an < 0,
      have bn_neg : bn < 0, from num_neg_of_equiv H an_neg,
      calc
        inv (mk an ad adp) ≡ mk (-ad) (-an) (neg_pos_of_neg an_neg) : inv_of_neg an_neg adp
                       ... ≡ mk (-bd) (-bn) (neg_pos_of_neg bn_neg) :
                             by rewrite [↑equiv at *, ▸*, *neg_mul_neg, mul.comm ad, mul.comm bd, H]
                       ... ≡ inv (mk bn bd bdp)                     : inv_of_neg bn_neg bdp)
    (assume an_zero : an = 0,
      have bn_zero : bn = 0, from num_eq_zero_of_equiv H an_zero,
      eq.subst (calc
        inv (mk an ad adp) = inv (mk 0 ad adp)  : {an_zero}
                       ... = zero               : inv_zero
                       ... = inv (mk 0 bd bdp)  : inv_zero
                       ... = inv (mk bn bd bdp) : bn_zero) !equiv.refl)
    (assume an_pos : an > 0,
      have bn_pos : bn > 0, from num_pos_of_equiv H an_pos,
      calc
        inv (mk an ad adp) ≡ mk ad an an_pos    : inv_of_pos an_pos adp
                       ... ≡ mk bd bn bn_pos    :
                                by rewrite [↑equiv at *, ▸*, mul.comm ad, mul.comm bd, H]
                       ... ≡ inv (mk bn bd bdp) : inv_of_pos bn_pos bdp)

/- properties -/

theorem add.comm (a b : prerat) : add a b ≡ add b a :=
by rewrite [↑add, ↑equiv, ▸*, add.comm, mul.comm (denom a)]

theorem add.assoc (a b c : prerat) : add (add a b) c ≡ add a (add b c) :=
by rewrite [↑add, ↑equiv, ▸*, *(mul.comm (num c)), *(λy, mul.comm y (denom a)), *mul.left_distrib,
            *mul.right_distrib, *mul.assoc, *add.assoc]

theorem add_zero (a : prerat) : add a zero ≡ a :=
by rewrite [↑add, ↑equiv, ↑zero, ↑of_int, ▸*, *mul_one, zero_mul, add_zero]

theorem add.left_inv (a : prerat) : add (neg a) a ≡ zero :=
by rewrite [↑add, ↑equiv, ↑neg, ↑zero, ↑of_int, ▸*, -neg_mul_eq_neg_mul, add.left_inv, *zero_mul]

theorem mul.comm (a b : prerat) : mul a b ≡ mul b a :=
by rewrite [↑mul, ↑equiv, mul.comm (num a), mul.comm (denom a)]

theorem mul.assoc (a b c : prerat) : mul (mul a b) c ≡ mul a (mul b c) :=
by rewrite [↑mul, ↑equiv, *mul.assoc]

theorem mul_one (a : prerat) : mul a one ≡ a :=
by rewrite [↑mul, ↑one, ↑of_int, ↑equiv, ▸*, *mul_one]

-- with the simplifier this will be easy
theorem mul.left_distrib (a b c : prerat) : mul a (add b c) ≡ add (mul a b) (mul a c) :=
begin
  rewrite [↑mul, ↑add, ↑equiv, ▸*, *mul.left_distrib, *mul.right_distrib, -*int.mul.assoc],
  apply sorry
end

theorem mul_inv_cancel : ∀{a : prerat}, ¬ a ≡ zero → mul a (inv a) ≡ one
| (mk an ad adp) :=
  assume H,
  let a := mk an ad adp in
  lt.by_cases
    (assume an_neg : an < 0,
      let ia := mk (-ad) (-an) (neg_pos_of_neg an_neg) in
      calc
        mul a (inv a) ≡ mul a ia : mul_equiv_mul !equiv.refl (inv_of_neg an_neg adp)
                  ... ≡ one      : begin
                                     esimp [equiv, num, denom, one, mul, of_int],
                                     rewrite [*int.mul_one, *int.one_mul, int.mul.comm,
                                              neg_mul_comm]
                                   end)
    (assume an_zero : an = 0, absurd (equiv_zero_of_num_eq_zero an_zero) H)
    (assume an_pos : an > 0,
      let ia := mk ad an an_pos in
      calc
        mul a (inv a) ≡ mul a ia : mul_equiv_mul !equiv.refl (inv_of_pos an_pos adp)
                  ... ≡ one      : begin
                                     esimp [equiv, num, denom, one, mul, of_int],
                                     rewrite [*int.mul_one, *int.one_mul, int.mul.comm]
                                   end)

theorem zero_not_equiv_one : ¬ zero ≡ one :=
begin
  esimp [equiv, zero, one, of_int],
  rewrite [zero_mul, int.mul_one],
  exact zero_ne_one
end

end prerat

/-
  the rationals
-/

definition rat : Type.{1} := quot prerat.setoid
notation `ℚ` := rat

local attribute prerat.setoid [instance]

namespace rat

/- operations -/

-- these coercions do not work: rat is not an inductive type
definition of_int [coercion] (i : ℤ) : ℚ := ⟦prerat.of_int i⟧
definition of_nat [coercion] (n : ℕ) : ℚ := ⟦prerat.of_int n⟧
definition of_num [coercion] [reducible] (n : num) : ℚ := of_int (int.of_num n)

definition add : ℚ → ℚ → ℚ :=
quot.lift₂
  (λa b : prerat, ⟦prerat.add a b⟧)
  (take a1 a2 b1 b2, assume H1 H2, quot.sound (prerat.add_equiv_add H1 H2))

definition mul : ℚ → ℚ → ℚ :=
quot.lift₂
  (λa b : prerat, ⟦prerat.mul a b⟧)
  (take a1 a2 b1 b2, assume H1 H2, quot.sound (prerat.mul_equiv_mul H1 H2))

definition neg : ℚ → ℚ :=
quot.lift
  (λa : prerat, ⟦prerat.neg a⟧)
  (take a1 a2, assume H, quot.sound (prerat.neg_equiv_neg H))

definition inv : ℚ → ℚ :=
quot.lift
  (λa : prerat, ⟦prerat.inv a⟧)
  (take a1 a2, assume H, quot.sound (prerat.inv_equiv_inv H))

definition zero := ⟦prerat.zero⟧
definition one := ⟦prerat.one⟧

infix `+`    := rat.add
infix `*`    := rat.mul
prefix `-`   := rat.neg
postfix `⁻¹` := rat.inv

definition sub (a b : rat) : rat := a + (-b)

infix `-`    := rat.sub

-- TODO: this is a workaround, since the coercions from numerals do not work
notation 0 := zero
notation 1 := one

/- properties -/

theorem add.comm (a b : ℚ) : a + b = b + a :=
quot.induction_on₂ a b (take u v, quot.sound !prerat.add.comm)

theorem add.assoc (a b c : ℚ) : a + b + c = a + (b + c) :=
quot.induction_on₃ a b c (take u v w, quot.sound !prerat.add.assoc)

theorem add_zero (a : ℚ) : a + 0 = a :=
quot.induction_on a (take u, quot.sound !prerat.add_zero)

theorem zero_add (a : ℚ) : 0 + a = a := !add.comm ▸ !add_zero

theorem add.left_inv (a : ℚ) : -a + a = 0 :=
quot.induction_on a (take u, quot.sound !prerat.add.left_inv)

theorem mul.comm (a b : ℚ) : a * b = b * a :=
quot.induction_on₂ a b (take u v, quot.sound !prerat.mul.comm)

theorem mul.assoc (a b c : ℚ) : a * b * c = a * (b * c) :=
quot.induction_on₃ a b c (take u v w, quot.sound !prerat.mul.assoc)

theorem mul_one (a : ℚ) : a * 1 = a :=
quot.induction_on a (take u, quot.sound !prerat.mul_one)

theorem one_mul (a : ℚ) : 1 * a = a := !mul.comm ▸ !mul_one

theorem mul.left_distrib (a b c : ℚ) : a * (b + c) = a * b + a * c :=
quot.induction_on₃ a b c (take u v w, quot.sound !prerat.mul.left_distrib)

theorem mul.right_distrib (a b c : ℚ) : (a + b) * c = a * c + b * c :=
by rewrite [mul.comm, mul.left_distrib, *mul.comm c]

theorem mul_inv_cancel {a : ℚ} : a ≠ 0 → a * a⁻¹ = 1 :=
quot.induction_on a
  (take u,
    assume H,
    quot.sound (!prerat.mul_inv_cancel (assume H1, H (quot.sound H1))))

theorem inv_mul_cancel {a : ℚ} (H : a ≠ 0) : a⁻¹ * a = 1 :=
!mul.comm ▸ mul_inv_cancel H

theorem zero_ne_one : (#rat 0 ≠ 1) :=
assume H, prerat.zero_not_equiv_one (quot.exact H)

definition has_decidable_eq [instance] : decidable_eq ℚ :=
take a b, quot.rec_on_subsingleton₂ a b
  (take u v,
     if H : prerat.num u * prerat.denom v = prerat.num v * prerat.denom u
       then decidable.inl (quot.sound H)
       else decidable.inr (assume H1, H (quot.exact H1)))

theorem inv_zero : inv 0 = 0 :=
quot.sound (prerat.inv_zero' ▸ !prerat.equiv.refl)

section
  open [classes] algebra

  protected definition discrete_field [instance] [reducible] : algebra.discrete_field rat :=
  ⦃algebra.discrete_field,
    add              := add,
    add_assoc        := add.assoc,
    zero             := 0,
    zero_add         := zero_add,
    add_zero         := add_zero,
    neg              := neg,
    add_left_inv     := add.left_inv,
    add_comm         := add.comm,
    mul              := mul,
    mul_assoc        := mul.assoc,
    one              := (of_num 1),
    one_mul          := one_mul,
    mul_one          := mul_one,
    left_distrib     := mul.left_distrib,
    right_distrib    := mul.right_distrib,
    mul_comm         := mul.comm,
    mul_inv_cancel   := @mul_inv_cancel,
    inv_mul_cancel   := @inv_mul_cancel,
    zero_ne_one      := zero_ne_one,
    inv_zero         := inv_zero,
    has_decidable_eq := has_decidable_eq⦄

  migrate from algebra with rat
    replacing sub → rat.sub
end

end rat
