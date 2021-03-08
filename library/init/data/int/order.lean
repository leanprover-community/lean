/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/
prelude
import init.data.int.basic init.data.ordering.basic

namespace int

def nonneg (a : ℤ) : Prop := int.cases_on a (assume n, true) (assume n, false)

protected def le (a b : ℤ) : Prop := nonneg (b - a)

instance : has_le int := ⟨int.le⟩

protected def lt (a b : ℤ) : Prop := (a + 1) ≤ b

instance : has_lt int := ⟨int.lt⟩

def decidable_nonneg (a : ℤ) : decidable (nonneg a) :=
int.cases_on a (assume a, decidable.true) (assume a, decidable.false)

instance decidable_le (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _

instance decidable_lt (a b : ℤ) : decidable (a < b) := decidable_nonneg _

lemma lt_iff_add_one_le (a b : ℤ) : a < b ↔ a + 1 ≤ b := iff.refl _

lemma nonneg.elim {a : ℤ} : nonneg a → ∃ n : ℕ, a = n :=
int.cases_on a (assume n H, exists.intro n rfl) (assume n', false.elim)

lemma nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
int.cases_on a (assume n, or.inl trivial) (assume n, or.inr trivial)

lemma le.intro_sub {a b : ℤ} {n : ℕ} (h : b - a = n) : a ≤ b :=
show nonneg (b - a), by rw h; trivial

local attribute [simp] int.sub_eq_add_neg int.add_assoc int.add_right_neg int.add_left_neg
  int.zero_add int.add_zero int.neg_add int.neg_neg int.neg_zero

lemma le.intro {a b : ℤ} {n : ℕ} (h : a + n = b) : a ≤ b :=
le.intro_sub (by rw [← h, int.add_comm]; simp)

lemma le.dest_sub {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, b - a = n := nonneg.elim h

lemma le.dest {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, a + n = b :=
match (le.dest_sub h) with
| ⟨n, h₁⟩ := exists.intro n begin rw [← h₁, int.add_comm], simp end
end

lemma le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
exists.elim (le.dest h) h'

protected lemma le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
or.imp_right
  (assume H : nonneg (-(b - a)),
   have -(b - a) = a - b, by simp [int.add_comm],
   show nonneg (a - b), from this ▸ H)
  (nonneg_or_nonneg_neg (b - a))

lemma coe_nat_le_coe_nat_of_le {m n : ℕ} (h : m ≤ n) : (↑m : ℤ) ≤ ↑n :=
match nat.le.dest h with
| ⟨k, (hk : m + k = n)⟩ := le.intro (begin rw [← hk], reflexivity end)
end

lemma le_of_coe_nat_le_coe_nat {m n : ℕ} (h : (↑m : ℤ) ≤ ↑n) : m ≤ n :=
le.elim h (assume k, assume hk : ↑m + ↑k = ↑n,
  have m + k = n, from int.coe_nat_inj ((int.coe_nat_add m k).trans hk),
  nat.le.intro this)

lemma coe_nat_le_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
iff.intro le_of_coe_nat_le_coe_nat coe_nat_le_coe_nat_of_le

lemma coe_zero_le (n : ℕ) : 0 ≤ (↑n : ℤ) :=
coe_nat_le_coe_nat_of_le n.zero_le

lemma eq_coe_of_zero_le {a : ℤ} (h : 0 ≤ a) : ∃ n : ℕ, a = n :=
by { have t := le.dest_sub h, simp at t, exact t }

lemma eq_succ_of_zero_lt {a : ℤ} (h : 0 < a) : ∃ n : ℕ, a = n.succ :=
let ⟨n, (h : ↑(1+n) = a)⟩ := le.dest h in
⟨n, by rw nat.add_comm at h; exact h.symm⟩

lemma lt_add_succ (a : ℤ) (n : ℕ) : a < a + ↑(nat.succ n) :=
le.intro (show a + 1 + n = a + nat.succ n,
  by { simp [int.coe_nat_eq, int.add_comm, int.add_left_comm], reflexivity })

lemma lt.intro {a b : ℤ} {n : ℕ} (h : a + nat.succ n = b) : a < b :=
h ▸ lt_add_succ a n

lemma lt.dest {a b : ℤ} (h : a < b) : ∃ n : ℕ, a + ↑(nat.succ n) = b :=
le.elim h (assume n, assume hn : a + 1 + n = b,
    exists.intro n begin rw [← hn, int.add_assoc, int.add_comm 1], reflexivity end)

lemma lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(nat.succ n) = b → P) : P :=
exists.elim (lt.dest h) h'

lemma coe_nat_lt_coe_nat_iff (n m : ℕ) : (↑n : ℤ) < ↑m ↔ n < m :=
begin rw [lt_iff_add_one_le, ← int.coe_nat_succ, coe_nat_le_coe_nat_iff], reflexivity end

lemma lt_of_coe_nat_lt_coe_nat {m n : ℕ} (h : (↑m : ℤ) < ↑n) : m < n :=
(coe_nat_lt_coe_nat_iff  _ _).mp h

lemma coe_nat_lt_coe_nat_of_lt {m n : ℕ} (h : m < n) : (↑m : ℤ) < ↑n :=
(coe_nat_lt_coe_nat_iff _ _).mpr h

/- show that the integers form an ordered additive group -/

protected lemma le_refl (a : ℤ) : a ≤ a :=
le.intro (int.add_zero a)

protected lemma le_trans {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
le.elim h₁ (assume n, assume hn : a + n = b,
le.elim h₂ (assume m, assume hm : b + m = c,
begin apply le.intro, rw [← hm, ← hn, int.add_assoc], reflexivity end))

protected lemma le_antisymm {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
le.elim h₁ (assume n, assume hn : a + n = b,
le.elim h₂ (assume m, assume hm : b + m = a,
  have a + ↑(n + m) = a + 0, by rw [int.coe_nat_add, ← int.add_assoc, hn, hm, int.add_zero a],
  have (↑(n + m) : ℤ) = 0, from int.add_left_cancel this,
  have n + m = 0, from int.coe_nat_inj this,
  have n = 0, from nat.eq_zero_of_add_eq_zero_right this,
  show a = b, begin rw [← hn, this, int.coe_nat_zero, int.add_zero a] end))

protected lemma lt_irrefl (a : ℤ) : ¬ a < a :=
assume : a < a,
lt.elim this (assume n, assume hn : a + nat.succ n = a,
  have a + nat.succ n = a + 0, by rw [hn, int.add_zero],
  have nat.succ n = 0, from int.coe_nat_inj (int.add_left_cancel this),
  show false, from nat.succ_ne_zero _ this)

protected lemma ne_of_lt {a b : ℤ} (h : a < b) : a ≠ b :=
(assume : a = b, absurd (begin rewrite this at h, exact h end) (int.lt_irrefl b))

lemma le_of_lt {a b : ℤ} (h : a < b) : a ≤ b :=
lt.elim h (assume n, assume hn : a + nat.succ n = b, le.intro hn)

protected lemma lt_iff_le_and_ne (a b : ℤ) : a < b ↔ (a ≤ b ∧ a ≠ b) :=
iff.intro
  (assume h, ⟨le_of_lt h, int.ne_of_lt h⟩)
  (assume ⟨aleb, aneb⟩,
    le.elim aleb (assume n, assume hn : a + n = b,
      have n ≠ 0,
        from (assume : n = 0, aneb begin rw [← hn, this, int.coe_nat_zero, int.add_zero] end),
      have n = nat.succ (nat.pred n),
        from eq.symm (nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero this)),
      lt.intro (begin rewrite this at hn, exact hn end)))

lemma lt_succ (a : ℤ) : a < a + 1 :=
int.le_refl (a + 1)

protected lemma add_le_add_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
le.elim h (assume n, assume hn : a + n = b,
  le.intro (show c + a + n = c + b, begin rw [int.add_assoc, hn] end))

protected lemma add_lt_add_left {a b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b :=
iff.mpr (int.lt_iff_le_and_ne _ _)
  (and.intro
    (int.add_le_add_left (le_of_lt h) _)
    (assume heq, int.lt_irrefl b begin rw int.add_left_cancel heq at h, exact h end))

protected lemma mul_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
le.elim ha (assume n, assume hn,
le.elim hb (assume m, assume hm,
  le.intro (show 0 + ↑n * ↑m = a * b, begin rw [← hn, ← hm], simp [int.zero_add] end)))

protected lemma mul_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
lt.elim ha (assume n, assume hn,
lt.elim hb (assume m, assume hm,
  lt.intro (show 0 + ↑(nat.succ (nat.succ n * m + n)) = a * b,
    begin rw [← hn, ← hm], simp [int.coe_nat_zero],
          rw [← int.coe_nat_mul], simp [nat.mul_succ, nat.succ_add] end)))

protected lemma zero_lt_one : (0 : ℤ) < 1 := trivial

protected lemma lt_iff_le_not_le {a b : ℤ} : a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
begin
simp [int.lt_iff_le_and_ne], split; intro h,
{ cases h with hab hn, split,
  { assumption },
  { intro hba, simp [int.le_antisymm hab hba] at *, contradiction } },
{ cases h with hab hn, split,
  { assumption },
  { intro h, simp [*] at * } }
end

instance : linear_order int :=
{ le              := int.le,
  le_refl         := int.le_refl,
  le_trans        := @int.le_trans,
  le_antisymm     := @int.le_antisymm,
  lt              := int.lt,
  lt_iff_le_not_le := @int.lt_iff_le_not_le,
  le_total        := int.le_total,
  decidable_eq    := int.decidable_eq,
  decidable_le    := int.decidable_le,
  decidable_lt    := int.decidable_lt }

lemma eq_nat_abs_of_zero_le {a : ℤ} (h : 0 ≤ a) : a = nat_abs a :=
let ⟨n, e⟩ := eq_coe_of_zero_le h in by rw e; refl

lemma le_nat_abs {a : ℤ} : a ≤ nat_abs a :=
or.elim (le_total 0 a)
  (λh, by rw eq_nat_abs_of_zero_le h; refl)
  (λh, le_trans h (coe_zero_le _))

lemma neg_succ_lt_zero (n : ℕ) : -[1+ n] < 0 :=
lt_of_not_ge $ λ h, let ⟨m, h⟩ := eq_coe_of_zero_le h in by contradiction

lemma eq_neg_succ_of_lt_zero : ∀ {a : ℤ}, a < 0 → ∃ n : ℕ, a = -[1+ n]
| (n : ℕ) h := absurd h (not_lt_of_ge (coe_zero_le _))
| -[1+ n] h := ⟨n, rfl⟩

/- int is an ordered add comm group -/

protected lemma eq_neg_of_eq_neg {a b : ℤ} (h : a = -b) : b = -a :=
by rw [h, int.neg_neg]

protected lemma neg_add_cancel_left (a b : ℤ) : -a + (a + b) = b :=
by rw [← int.add_assoc, int.add_left_neg, int.zero_add]

protected lemma add_neg_cancel_left (a b : ℤ) : a + (-a + b) = b :=
by rw [← int.add_assoc, int.add_right_neg, int.zero_add]

protected lemma add_neg_cancel_right (a b : ℤ) : a + b + -b = a :=
by rw [int.add_assoc, int.add_right_neg, int.add_zero]

protected lemma neg_add_cancel_right (a b : ℤ) : a + -b + b = a :=
by rw [int.add_assoc, int.add_left_neg, int.add_zero]

protected lemma sub_self (a : ℤ) : a - a = 0 :=
by rw [int.sub_eq_add_neg, int.add_right_neg]

protected lemma sub_eq_zero_of_eq {a b : ℤ} (h : a = b) : a - b = 0 :=
by rw [h, int.sub_self]

protected lemma eq_of_sub_eq_zero {a b : ℤ} (h : a - b = 0) : a = b :=
have 0 + b = b, by rw int.zero_add,
have (a - b) + b = b, by rwa h,
by rwa [int.sub_eq_add_neg, int.neg_add_cancel_right] at this

protected lemma sub_eq_zero_iff_eq {a b : ℤ} : a - b = 0 ↔ a = b :=
⟨int.eq_of_sub_eq_zero, int.sub_eq_zero_of_eq⟩

@[simp] protected lemma neg_eq_of_add_eq_zero {a b : ℤ} (h : a + b = 0) : -a = b :=
by rw [← int.add_zero (-a), ←h, ←int.add_assoc, int.add_left_neg, int.zero_add]

protected lemma neg_mul_eq_neg_mul (a b : ℤ) : -(a * b) = -a * b :=
int.neg_eq_of_add_eq_zero
  begin rw [← int.distrib_right, int.add_right_neg, int.zero_mul] end

protected lemma neg_mul_eq_mul_neg (a b : ℤ) : -(a * b) = a * -b :=
int.neg_eq_of_add_eq_zero
  begin rw [← int.distrib_left, int.add_right_neg, int.mul_zero] end

lemma neg_mul_eq_neg_mul_symm (a b : ℤ) : - a * b = - (a * b) :=
eq.symm (int.neg_mul_eq_neg_mul a b)

lemma mul_neg_eq_neg_mul_symm (a b : ℤ) : a * - b = - (a * b) :=
eq.symm (int.neg_mul_eq_mul_neg a b)

local attribute [simp] neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm

protected lemma neg_mul_neg (a b : ℤ) : -a * -b = a * b :=
by simp

protected lemma neg_mul_comm (a b : ℤ) : -a * b = a * -b :=
by simp

protected lemma mul_sub (a b c : ℤ) : a * (b - c) = a * b - a * c :=
calc
   a * (b - c) = a * b + a * -c : int.distrib_left a b (-c)
           ... = a * b - a * c  : by simp

protected lemma sub_mul (a b c : ℤ) : (a - b) * c = a * c - b * c :=
calc
  (a - b) * c = a * c  + -b * c : int.distrib_right a (-b) c
          ... = a * c - b * c   : by simp

section

protected lemma le_of_add_le_add_left {a b c : ℤ} (h : a + b ≤ a + c) : b ≤ c :=
have -a + (a + b) ≤ -a + (a + c), from int.add_le_add_left h _,
begin simp [int.neg_add_cancel_left] at this, assumption end

protected lemma lt_of_add_lt_add_left {a b c : ℤ} (h : a + b < a + c) : b < c :=
have -a + (a + b) < -a + (a + c), from int.add_lt_add_left h _,
begin simp [int.neg_add_cancel_left] at this, assumption end

protected lemma add_le_add_right {a b : ℤ} (h : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
int.add_comm c a ▸ int.add_comm c b ▸ int.add_le_add_left h c

protected theorem add_lt_add_right {a b : ℤ} (h : a < b) (c : ℤ) : a + c < b + c :=
begin
 rw [int.add_comm a c, int.add_comm b c],
 exact (int.add_lt_add_left h c)
end

protected lemma add_le_add {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
le_trans (int.add_le_add_right h₁ c) (int.add_le_add_left h₂ b)

protected lemma le_add_of_nonneg_right {a b : ℤ} (h : 0 ≤ b) : a ≤ a + b :=
have a + b ≥ a + 0, from int.add_le_add_left h a,
by rwa int.add_zero at this

protected lemma le_add_of_nonneg_left {a b : ℤ} (h : 0 ≤ b) : a ≤ b + a :=
have 0 + a ≤ b + a, from int.add_le_add_right h a,
by rwa int.zero_add at this

protected lemma add_lt_add {a b c d : ℤ} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
lt_trans (int.add_lt_add_right h₁ c) (int.add_lt_add_left h₂ b)

protected lemma add_lt_add_of_le_of_lt {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
lt_of_le_of_lt (int.add_le_add_right h₁ c) (int.add_lt_add_left h₂ b)

protected lemma add_lt_add_of_lt_of_le {a b c d : ℤ} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
lt_of_lt_of_le (int.add_lt_add_right h₁ c) (int.add_le_add_left h₂ b)

protected lemma lt_add_of_pos_right (a : ℤ) {b : ℤ} (h : 0 < b) : a < a + b :=
have a + 0 < a + b, from int.add_lt_add_left h a,
by rwa [int.add_zero] at this

protected lemma lt_add_of_pos_left (a : ℤ) {b : ℤ} (h : 0 < b) : a < b + a :=
have 0 + a < b + a, from int.add_lt_add_right h a,
by rwa [int.zero_add] at this

protected lemma le_of_add_le_add_right {a b c : ℤ} (h : a + b ≤ c + b) : a ≤ c :=
int.le_of_add_le_add_left
  (show b + a ≤ b + c, begin rw [int.add_comm b a, int.add_comm b c], assumption end)

protected lemma lt_of_add_lt_add_right {a b c : ℤ} (h : a + b < c + b) : a < c :=
int.lt_of_add_lt_add_left
  (show b + a < b + c, begin rw [int.add_comm b a, int.add_comm b c], assumption end)

-- here we start using properties of zero.
protected lemma add_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
int.zero_add (0:ℤ) ▸ (int.add_le_add ha hb)

protected lemma add_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  int.zero_add (0:ℤ) ▸ (int.add_lt_add ha hb)

protected lemma add_pos_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
int.zero_add (0:ℤ) ▸ (int.add_lt_add_of_lt_of_le ha hb)

protected lemma add_pos_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
int.zero_add (0:ℤ) ▸ (int.add_lt_add_of_le_of_lt ha hb)

protected lemma add_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
int.zero_add (0:ℤ) ▸ (int.add_le_add ha hb)

protected lemma add_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
int.zero_add (0:ℤ) ▸ (int.add_lt_add ha hb)

protected lemma add_neg_of_neg_of_nonpos {a b : ℤ} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
int.zero_add (0:ℤ) ▸ (int.add_lt_add_of_lt_of_le ha hb)

protected lemma add_neg_of_nonpos_of_neg {a b : ℤ} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
int.zero_add (0:ℤ) ▸ (int.add_lt_add_of_le_of_lt ha hb)

protected lemma lt_add_of_le_of_pos {a b c : ℤ} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
int.add_zero b ▸ int.add_lt_add_of_le_of_lt hbc ha

protected lemma sub_add_cancel (a b : ℤ) : a - b + b = a :=
int.neg_add_cancel_right a b

protected lemma add_sub_cancel (a b : ℤ) : a + b - b = a :=
int.add_neg_cancel_right a b

protected lemma add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c) :=
by rw [int.sub_eq_add_neg, int.add_assoc, ←int.sub_eq_add_neg]

protected lemma neg_le_neg {a b : ℤ} (h : a ≤ b) : -b ≤ -a :=
have 0 ≤ -a + b,           from int.add_left_neg a ▸ int.add_le_add_left h (-a),
have 0 + -b ≤ -a + b + -b, from int.add_le_add_right this (-b),
by rwa [int.add_neg_cancel_right, int.zero_add] at this

protected lemma le_of_neg_le_neg {a b : ℤ} (h : -b ≤ -a) : a ≤ b :=
suffices -(-a) ≤ -(-b), from
  begin simp [int.neg_neg] at this, assumption end,
int.neg_le_neg h

protected lemma nonneg_of_neg_nonpos {a : ℤ} (h : -a ≤ 0) : 0 ≤ a :=
have -a ≤ -0, by rwa int.neg_zero,
int.le_of_neg_le_neg this

protected lemma neg_nonpos_of_nonneg {a : ℤ} (h : 0 ≤ a) : -a ≤ 0 :=
have -a ≤ -0, from int.neg_le_neg h,
by rwa int.neg_zero at this

protected lemma nonpos_of_neg_nonneg {a : ℤ} (h : 0 ≤ -a) : a ≤ 0 :=
have -0 ≤ -a, by rwa int.neg_zero,
int.le_of_neg_le_neg this

protected lemma neg_nonneg_of_nonpos {a : ℤ} (h : a ≤ 0) : 0 ≤ -a :=
have -0 ≤ -a, from int.neg_le_neg h,
by rwa int.neg_zero at this

protected lemma neg_lt_neg {a b : ℤ} (h : a < b) : -b < -a :=
have 0 < -a + b, from int.add_left_neg a ▸ int.add_lt_add_left h (-a),
have 0 + -b < -a + b + -b, from int.add_lt_add_right this (-b),
by rwa [int.add_neg_cancel_right, int.zero_add] at this

protected lemma lt_of_neg_lt_neg {a b : ℤ} (h : -b < -a) : a < b :=
int.neg_neg a ▸ int.neg_neg b ▸ int.neg_lt_neg h

protected lemma pos_of_neg_neg {a : ℤ} (h : -a < 0) : 0 < a :=
have -a < -0, by rwa int.neg_zero,
int.lt_of_neg_lt_neg this

protected lemma neg_neg_of_pos {a : ℤ} (h : 0 < a) : -a < 0 :=
have -a < -0, from int.neg_lt_neg h,
by rwa int.neg_zero at this

protected lemma neg_of_neg_pos {a : ℤ} (h : 0 < -a) : a < 0 :=
have -0 < -a, by rwa int.neg_zero,
int.lt_of_neg_lt_neg this

protected lemma neg_pos_of_neg {a : ℤ} (h : a < 0) : 0 < -a :=
have -0 < -a, from int.neg_lt_neg h,
by rwa int.neg_zero at this

protected lemma le_neg_of_le_neg {a b : ℤ} (h : a ≤ -b) : b ≤ -a :=
begin
  have h := int.neg_le_neg h,
  rwa int.neg_neg at h
end

protected lemma neg_le_of_neg_le {a b : ℤ} (h : -a ≤ b) : -b ≤ a :=
begin
  have h := int.neg_le_neg h,
  rwa int.neg_neg at h
end

protected lemma lt_neg_of_lt_neg {a b : ℤ} (h : a < -b) : b < -a :=
begin
  have h := int.neg_lt_neg h,
  rwa int.neg_neg at h
end

protected lemma neg_lt_of_neg_lt {a b : ℤ} (h : -a < b) : -b < a :=
begin
  have h := int.neg_lt_neg h,
  rwa int.neg_neg at h
end

protected lemma sub_nonneg_of_le {a b : ℤ} (h : b ≤ a) : 0 ≤ a - b :=
begin
  have h := int.add_le_add_right h (-b),
  rwa int.add_right_neg at h
end

protected lemma le_of_sub_nonneg {a b : ℤ} (h : 0 ≤ a - b) : b ≤ a :=
begin
  have h := int.add_le_add_right h b,
  rwa [int.sub_add_cancel, int.zero_add] at h
end

protected lemma sub_nonpos_of_le {a b : ℤ} (h : a ≤ b) : a - b ≤ 0 :=
begin
  have h := int.add_le_add_right h (-b),
  rwa int.add_right_neg at h
end

protected lemma le_of_sub_nonpos {a b : ℤ} (h : a - b ≤ 0) : a ≤ b :=
begin
  have h := int.add_le_add_right h b,
  rwa [int.sub_add_cancel, int.zero_add] at h
end

protected lemma sub_pos_of_lt {a b : ℤ} (h : b < a) : 0 < a - b :=
begin
  have h := int.add_lt_add_right h (-b),
  rwa int.add_right_neg at h
end

protected lemma lt_of_sub_pos {a b : ℤ} (h : 0 < a - b) : b < a :=
begin
  have h := int.add_lt_add_right h b,
  rwa [int.sub_add_cancel, int.zero_add] at h
end

protected lemma sub_neg_of_lt {a b : ℤ} (h : a < b) : a - b < 0 :=
begin
  have h := int.add_lt_add_right h (-b),
  rwa int.add_right_neg at h
end

protected lemma lt_of_sub_neg {a b : ℤ} (h : a - b < 0) : a < b :=
begin
  have h := int.add_lt_add_right h b,
  rwa [int.sub_add_cancel, int.zero_add] at h
end

protected lemma add_le_of_le_neg_add {a b c : ℤ} (h : b ≤ -a + c) : a + b ≤ c :=
begin
  have h := int.add_le_add_left h a,
  rwa int.add_neg_cancel_left at h
end

protected lemma le_neg_add_of_add_le {a b c : ℤ} (h : a + b ≤ c) : b ≤ -a + c :=
begin
  have h := int.add_le_add_left h (-a),
  rwa int.neg_add_cancel_left at h
end

protected lemma add_le_of_le_sub_left {a b c : ℤ} (h : b ≤ c - a) : a + b ≤ c :=
begin
  have h := int.add_le_add_left h a,
  rwa [← int.add_sub_assoc, int.add_comm a c, int.add_sub_cancel] at h
end

protected lemma le_sub_left_of_add_le {a b c : ℤ} (h : a + b ≤ c) : b ≤ c - a :=
begin
  have h := int.add_le_add_right h (-a),
  rwa [int.add_comm a b, int.add_neg_cancel_right] at h
end

protected lemma add_le_of_le_sub_right {a b c : ℤ} (h : a ≤ c - b) : a + b ≤ c :=
begin
  have h := int.add_le_add_right h b,
  rwa int.sub_add_cancel at h
end

protected lemma le_sub_right_of_add_le {a b c : ℤ} (h : a + b ≤ c) : a ≤ c - b :=
begin
  have h := int.add_le_add_right h (-b),
  rwa int.add_neg_cancel_right at h
end

protected lemma le_add_of_neg_add_le {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c :=
begin
  have h := int.add_le_add_left h b,
  rwa int.add_neg_cancel_left at h
end

protected lemma neg_add_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c :=
begin
  have h := int.add_le_add_left h (-b),
  rwa int.neg_add_cancel_left at h
end

protected lemma le_add_of_sub_left_le {a b c : ℤ} (h : a - b ≤ c) : a ≤ b + c :=
begin
  have h := int.add_le_add_right h b,
  rwa [int.sub_add_cancel, int.add_comm] at h
end

protected lemma sub_left_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : a - b ≤ c :=
begin
  have h := int.add_le_add_right h (-b),
  rwa [int.add_comm b c, int.add_neg_cancel_right] at h
end

protected lemma le_add_of_sub_right_le {a b c : ℤ} (h : a - c ≤ b) : a ≤ b + c :=
begin
  have h := int.add_le_add_right h c,
  rwa int.sub_add_cancel at h
end

protected lemma sub_right_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : a - c ≤ b :=
begin
  have h := int.add_le_add_right h (-c),
  rwa int.add_neg_cancel_right at h
end

protected lemma le_add_of_neg_add_le_left {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c :=
begin
  rw int.add_comm at h,
  exact int.le_add_of_sub_left_le h
end

protected lemma neg_add_le_left_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c :=
begin
  rw int.add_comm,
  exact int.sub_left_le_of_le_add h
end

protected lemma le_add_of_neg_add_le_right {a b c : ℤ} (h : -c + a ≤ b) : a ≤ b + c :=
begin
  rw int.add_comm at h,
  exact int.le_add_of_sub_right_le h
end

protected lemma neg_add_le_right_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -c + a ≤ b :=
begin
  rw int.add_comm at h,
  exact int.neg_add_le_left_of_le_add h
end

protected lemma le_add_of_neg_le_sub_left {a b c : ℤ} (h : -a ≤ b - c) : c ≤ a + b :=
int.le_add_of_neg_add_le_left (int.add_le_of_le_sub_right h)

protected lemma neg_le_sub_left_of_le_add {a b c : ℤ} (h : c ≤ a + b) : -a ≤ b - c :=
begin
  have h := int.le_neg_add_of_add_le (int.sub_left_le_of_le_add h),
  rwa int.add_comm at h
end

protected lemma le_add_of_neg_le_sub_right {a b c : ℤ} (h : -b ≤ a - c) : c ≤ a + b :=
int.le_add_of_sub_right_le (int.add_le_of_le_sub_left h)

protected lemma neg_le_sub_right_of_le_add {a b c : ℤ} (h : c ≤ a + b) : -b ≤ a - c :=
int.le_sub_left_of_add_le (int.sub_right_le_of_le_add h)

protected lemma sub_le_of_sub_le {a b c : ℤ} (h : a - b ≤ c) : a - c ≤ b :=
int.sub_left_le_of_le_add (int.le_add_of_sub_right_le h)

protected lemma sub_le_sub_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
int.add_le_add_left (int.neg_le_neg h) c

protected lemma sub_le_sub_right {a b : ℤ} (h : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
int.add_le_add_right h (-c)

protected lemma sub_le_sub {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
int.add_le_add hab (int.neg_le_neg hcd)

protected lemma add_lt_of_lt_neg_add {a b c : ℤ} (h : b < -a + c) : a + b < c :=
begin
  have h := int.add_lt_add_left h a,
  rwa int.add_neg_cancel_left at h
end

protected lemma lt_neg_add_of_add_lt {a b c : ℤ} (h : a + b < c) : b < -a + c :=
begin
  have h := int.add_lt_add_left h (-a),
  rwa int.neg_add_cancel_left at h
end

protected lemma add_lt_of_lt_sub_left {a b c : ℤ} (h : b < c - a) : a + b < c :=
begin
  have h := int.add_lt_add_left h a,
  rwa [← int.add_sub_assoc, int.add_comm a c, int.add_sub_cancel] at h
end

protected lemma lt_sub_left_of_add_lt {a b c : ℤ} (h : a + b < c) : b < c - a :=
begin
  have h := int.add_lt_add_right h (-a),
  rwa [int.add_comm a b, int.add_neg_cancel_right] at h
end

protected lemma add_lt_of_lt_sub_right {a b c : ℤ} (h : a < c - b) : a + b < c :=
begin
  have h := int.add_lt_add_right h b,
  rwa int.sub_add_cancel at h
end

protected lemma lt_sub_right_of_add_lt {a b c : ℤ} (h : a + b < c) : a < c - b :=
begin
  have h := int.add_lt_add_right h (-b),
  rwa int.add_neg_cancel_right at h
end

protected lemma lt_add_of_neg_add_lt {a b c : ℤ} (h : -b + a < c) : a < b + c :=
begin
  have h := int.add_lt_add_left h b,
  rwa int.add_neg_cancel_left at h
end

protected lemma neg_add_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : -b + a < c :=
begin
  have h := int.add_lt_add_left h (-b),
  rwa int.neg_add_cancel_left at h
end

protected lemma lt_add_of_sub_left_lt {a b c : ℤ} (h : a - b < c) : a < b + c :=
begin
  have h := int.add_lt_add_right h b,
  rwa [int.sub_add_cancel, int.add_comm] at h
end

protected lemma sub_left_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : a - b < c :=
begin
  have h := int.add_lt_add_right h (-b),
  rwa [int.add_comm b c, int.add_neg_cancel_right] at h
end

protected lemma lt_add_of_sub_right_lt {a b c : ℤ} (h : a - c < b) : a < b + c :=
begin
  have h := int.add_lt_add_right h c,
  rwa int.sub_add_cancel at h
end

protected lemma sub_right_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : a - c < b :=
begin
  have h := int.add_lt_add_right h (-c),
  rwa int.add_neg_cancel_right at h
end

protected lemma lt_add_of_neg_add_lt_left {a b c : ℤ} (h : -b + a < c) : a < b + c :=
begin
  rw int.add_comm at h,
  exact int.lt_add_of_sub_left_lt h
end

protected lemma neg_add_lt_left_of_lt_add {a b c : ℤ} (h : a < b + c) : -b + a < c :=
begin
  rw int.add_comm,
  exact int.sub_left_lt_of_lt_add h
end

protected lemma lt_add_of_neg_add_lt_right {a b c : ℤ} (h : -c + a < b) : a < b + c :=
begin
  rw int.add_comm at h,
  exact int.lt_add_of_sub_right_lt h
end

protected lemma neg_add_lt_right_of_lt_add {a b c : ℤ} (h : a < b + c) : -c + a < b :=
begin
  rw int.add_comm at h,
  exact int.neg_add_lt_left_of_lt_add h
end

protected lemma lt_add_of_neg_lt_sub_left {a b c : ℤ} (h : -a < b - c) : c < a + b :=
int.lt_add_of_neg_add_lt_left (int.add_lt_of_lt_sub_right h)

protected lemma neg_lt_sub_left_of_lt_add {a b c : ℤ} (h : c < a + b) : -a < b - c :=
begin
  have h := int.lt_neg_add_of_add_lt (int.sub_left_lt_of_lt_add h),
  rwa int.add_comm at h
end

protected lemma lt_add_of_neg_lt_sub_right {a b c : ℤ} (h : -b < a - c) : c < a + b :=
int.lt_add_of_sub_right_lt (int.add_lt_of_lt_sub_left h)

protected lemma neg_lt_sub_right_of_lt_add {a b c : ℤ} (h : c < a + b) : -b < a - c :=
int.lt_sub_left_of_add_lt (int.sub_right_lt_of_lt_add h)

protected lemma sub_lt_of_sub_lt {a b c : ℤ} (h : a - b < c) : a - c < b :=
int.sub_left_lt_of_lt_add (int.lt_add_of_sub_right_lt h)

protected lemma sub_lt_sub_left {a b : ℤ} (h : a < b) (c : ℤ) : c - b < c - a :=
int.add_lt_add_left (int.neg_lt_neg h) c

protected lemma sub_lt_sub_right {a b : ℤ} (h : a < b) (c : ℤ) : a - c < b - c :=
int.add_lt_add_right h (-c)

protected lemma sub_lt_sub {a b c d : ℤ} (hab : a < b) (hcd : c < d) : a - d < b - c :=
int.add_lt_add hab (int.neg_lt_neg hcd)

protected lemma sub_lt_sub_of_le_of_lt {a b c d : ℤ} (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
int.add_lt_add_of_le_of_lt hab (int.neg_lt_neg hcd)

protected lemma sub_lt_sub_of_lt_of_le {a b c d : ℤ} (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
int.add_lt_add_of_lt_of_le hab (int.neg_le_neg hcd)

protected lemma sub_le_self (a : ℤ) {b : ℤ} (h : 0 ≤ b) : a - b ≤ a :=
calc
  a - b = a + -b : rfl
    ... ≤ a + 0  : int.add_le_add_left (int.neg_nonpos_of_nonneg h) _
    ... = a      : by rw int.add_zero

protected lemma sub_lt_self (a : ℤ) {b : ℤ} (h : 0 < b) : a - b < a :=
calc
  a - b = a + -b : rfl
    ... < a + 0  : int.add_lt_add_left (int.neg_neg_of_pos h) _
    ... = a      : by rw int.add_zero

protected lemma add_le_add_three {a b c d e f : ℤ} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
      a + b + c ≤ d + e + f :=
begin
  apply le_trans,
  apply int.add_le_add,
  apply int.add_le_add,
  assumption',
  apply le_refl
end

end

/- missing facts -/

protected lemma mul_lt_mul_of_pos_left {a b c : ℤ}
       (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
have 0 < b - a,       from int.sub_pos_of_lt h₁,
have 0 < c * (b - a), from int.mul_pos h₂ this,
begin
  rw int.mul_sub at this,
  exact int.lt_of_sub_pos this
end

protected lemma mul_lt_mul_of_pos_right {a b c : ℤ}
      (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
have 0 < b - a,       from int.sub_pos_of_lt h₁,
have 0 < (b - a) * c, from int.mul_pos this h₂,
begin
  rw int.sub_mul at this,
  exact int.lt_of_sub_pos this
end

protected lemma mul_le_mul_of_nonneg_left {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
begin
  by_cases hba : b ≤ a, { simp [le_antisymm hba h₁] },
  by_cases hc0 : c ≤ 0, { simp [le_antisymm hc0 h₂, int.zero_mul] },
  exact (le_not_le_of_lt (int.mul_lt_mul_of_pos_left
    (lt_of_le_not_le h₁ hba) (lt_of_le_not_le h₂ hc0))).left,
end

protected lemma mul_le_mul_of_nonneg_right {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
begin
  by_cases hba : b ≤ a, { simp [le_antisymm hba h₁] },
  by_cases hc0 : c ≤ 0, { simp [le_antisymm hc0 h₂, int.mul_zero] },
  exact (le_not_le_of_lt
    (int.mul_lt_mul_of_pos_right (lt_of_le_not_le h₁ hba) (lt_of_le_not_le h₂ hc0))).left,
end

-- TODO: there are four variations, depending on which variables we assume to be nonneg
protected lemma mul_le_mul {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) :
  a * b ≤ c * d :=
calc
  a * b ≤ c * b : int.mul_le_mul_of_nonneg_right hac nn_b
    ... ≤ c * d : int.mul_le_mul_of_nonneg_left hbd nn_c

protected lemma mul_nonpos_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 :=
have h : a * b ≤ a * 0, from int.mul_le_mul_of_nonneg_left hb ha,
by rwa int.mul_zero at h

protected lemma mul_nonpos_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 :=
have h : a * b ≤ 0 * b, from int.mul_le_mul_of_nonneg_right ha hb,
by rwa int.zero_mul at h

protected lemma mul_lt_mul {a b c d : ℤ} (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b)
  (nn_c : 0 ≤ c) : a * b < c * d :=
calc
  a * b < c * b : int.mul_lt_mul_of_pos_right hac pos_b
    ... ≤ c * d : int.mul_le_mul_of_nonneg_left hbd nn_c

protected lemma mul_lt_mul' {a b c d : ℤ} (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) :
       a * b < c * d :=
calc
   a * b ≤ c * b : int.mul_le_mul_of_nonneg_right h1 h3
     ... < c * d : int.mul_lt_mul_of_pos_left h2 h4

protected lemma mul_neg_of_pos_of_neg {a b : ℤ} (ha : 0 < a) (hb : b < 0) : a * b < 0 :=
have h : a * b < a * 0, from int.mul_lt_mul_of_pos_left hb ha,
by rwa int.mul_zero at h

protected lemma mul_neg_of_neg_of_pos {a b : ℤ} (ha : a < 0) (hb : 0 < b) : a * b < 0 :=
have h : a * b < 0 * b, from int.mul_lt_mul_of_pos_right ha hb,
by rwa int.zero_mul at  h

protected lemma mul_le_mul_of_nonpos_right {a b c : ℤ} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
have -c ≥ 0,              from int.neg_nonneg_of_nonpos hc,
have b * -c ≤ a * -c,     from int.mul_le_mul_of_nonneg_right h this,
have -(b * c) ≤ -(a * c), by rwa [← int.neg_mul_eq_mul_neg, ← int.neg_mul_eq_mul_neg] at this,
int.le_of_neg_le_neg this

protected lemma mul_nonneg_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b :=
have 0 * b ≤ a * b, from int.mul_le_mul_of_nonpos_right ha hb,
by rwa int.zero_mul at this

protected lemma mul_lt_mul_of_neg_left {a b c : ℤ} (h : b < a) (hc : c < 0) : c * a < c * b :=
have -c > 0,              from int.neg_pos_of_neg hc,
have -c * b < -c * a,     from int.mul_lt_mul_of_pos_left h this,
have -(c * b) < -(c * a), by rwa [← int.neg_mul_eq_neg_mul, ← int.neg_mul_eq_neg_mul] at this,
int.lt_of_neg_lt_neg this

protected lemma mul_lt_mul_of_neg_right {a b c : ℤ} (h : b < a) (hc : c < 0) : a * c < b * c :=
have -c > 0,              from int.neg_pos_of_neg hc,
have b * -c < a * -c,     from int.mul_lt_mul_of_pos_right h this,
have -(b * c) < -(a * c), by rwa [← int.neg_mul_eq_mul_neg, ← int.neg_mul_eq_mul_neg] at this,
int.lt_of_neg_lt_neg this

protected lemma mul_pos_of_neg_of_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
have 0 * b < a * b, from int.mul_lt_mul_of_neg_right ha hb,
by rwa int.zero_mul at this

protected lemma mul_self_le_mul_self {a b : ℤ} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
int.mul_le_mul h2 h2 h1 (le_trans h1 h2)

protected lemma mul_self_lt_mul_self {a b : ℤ} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
int.mul_lt_mul' (le_of_lt h2) h2 h1 (lt_of_le_of_lt h1 h2)

/- more facts specific to int -/

theorem of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n := trivial

theorem coe_succ_pos (n : nat) : 0 < (nat.succ n : ℤ) :=
coe_nat_lt_coe_nat_of_lt (nat.succ_pos _)

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -n :=
let ⟨n, h⟩ := eq_coe_of_zero_le (int.neg_nonneg_of_nonpos H) in
⟨n, int.eq_neg_of_eq_neg h.symm⟩

theorem nat_abs_of_nonneg {a : ℤ} (H : 0 ≤ a) : (nat_abs a : ℤ) = a :=
match a, eq_coe_of_zero_le H with ._, ⟨n, rfl⟩ := rfl end

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : (nat_abs a : ℤ) = -a :=
by rw [← nat_abs_neg, nat_abs_of_nonneg (int.neg_nonneg_of_nonpos H)]

theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b := H

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b := H

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
int.add_le_add_right H 1

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
int.le_of_add_le_add_right H

theorem sub_one_le_of_lt {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
int.sub_right_lt_of_lt_add $ lt_add_one_of_le H

theorem lt_of_sub_one_le {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
le_of_lt_add_one $ int.lt_add_of_sub_right_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
int.le_sub_right_of_add_le H

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
int.add_le_of_le_sub_right H

theorem sign_of_succ (n : nat) : sign (nat.succ n) = 1 := rfl

theorem sign_eq_one_of_pos {a : ℤ} (h : 0 < a) : sign a = 1 :=
match a, eq_succ_of_zero_lt h with ._, ⟨n, rfl⟩ := rfl end

theorem sign_eq_neg_one_of_neg {a : ℤ} (h : a < 0) : sign a = -1 :=
match a, eq_neg_succ_of_lt_zero h with ._, ⟨n, rfl⟩ := rfl end

lemma eq_zero_of_sign_eq_zero : Π {a : ℤ}, sign a = 0 → a = 0
| 0 _ := rfl

theorem pos_of_sign_eq_one : ∀ {a : ℤ}, sign a = 1 → 0 < a
| (n+1:ℕ) _ := coe_nat_lt_coe_nat_of_lt (nat.succ_pos _)

theorem neg_of_sign_eq_neg_one : ∀ {a : ℤ}, sign a = -1 → a < 0
| (n+1:ℕ) h := match h with end
| 0       h := match h with end
| -[1+ n] _ := neg_succ_lt_zero _

theorem sign_eq_one_iff_pos (a : ℤ) : sign a = 1 ↔ 0 < a :=
⟨pos_of_sign_eq_one, sign_eq_one_of_pos⟩

theorem sign_eq_neg_one_iff_neg (a : ℤ) : sign a = -1 ↔ a < 0 :=
⟨neg_of_sign_eq_neg_one, sign_eq_neg_one_of_neg⟩

theorem sign_eq_zero_iff_zero (a : ℤ) : sign a = 0 ↔ a = 0 :=
⟨eq_zero_of_sign_eq_zero, λ h, by rw [h, sign_zero]⟩

protected lemma eq_zero_or_eq_zero_of_mul_eq_zero
        {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
match decidable.lt_trichotomy 0 a with
| or.inl hlt₁          :=
  match decidable.lt_trichotomy 0 b with
  | or.inl hlt₂          :=
    have 0 < a * b, from int.mul_pos hlt₁ hlt₂,
    begin rw h at this, exact absurd this (lt_irrefl _) end
  | or.inr (or.inl heq₂) := or.inr heq₂.symm
  | or.inr (or.inr hgt₂) :=
    have 0 > a * b, from int.mul_neg_of_pos_of_neg hlt₁ hgt₂,
    begin rw h at this, exact absurd this (lt_irrefl _)  end
  end
| or.inr (or.inl heq₁) := or.inl heq₁.symm
| or.inr (or.inr hgt₁) :=
  match decidable.lt_trichotomy 0 b with
  | or.inl hlt₂          :=
    have 0 > a * b, from int.mul_neg_of_neg_of_pos hgt₁ hlt₂,
    begin rw h at this, exact absurd this (lt_irrefl _)  end
  | or.inr (or.inl heq₂) := or.inr heq₂.symm
  | or.inr (or.inr hgt₂) :=
    have 0 < a * b, from int.mul_pos_of_neg_of_neg hgt₁ hgt₂,
    begin rw h at this, exact absurd this (lt_irrefl _)  end
  end
end

protected lemma eq_of_mul_eq_mul_right {a b c : ℤ} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
have b * a - c * a = 0, from int.sub_eq_zero_of_eq h,
have (b - c) * a = 0,   by rw [int.sub_mul, this],
have b - c = 0,         from (int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
int.eq_of_sub_eq_zero this

protected lemma eq_of_mul_eq_mul_left {a b c : ℤ} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
have a * b - a * c = 0, from int.sub_eq_zero_of_eq h,
have a * (b - c) = 0,   by rw [int.mul_sub, this],
have b - c = 0,         from (int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
int.eq_of_sub_eq_zero this

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
int.eq_of_mul_eq_mul_right Hpos (by rw [int.one_mul, H])

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
int.eq_of_mul_eq_mul_left Hpos (by rw [int.mul_one, H])

end int
