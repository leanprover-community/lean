/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Auxiliary lemmas used to compare int numerals.
-/
prelude
import init.data.int.order

namespace int
/- Auxiliary lemmas for proving that to int numerals are different -/

/- 1. Lemmas for reducing the problem to the case where the numerals are positive -/

protected lemma ne_neg_of_ne {a b : ℤ} : a ≠ b → -a ≠ -b :=
λ h₁ h₂, absurd (int.neg_inj h₂) h₁

protected lemma neg_ne_zero_of_ne {a : ℤ} : a ≠ 0 → -a ≠ 0 :=
λ h₁ h₂,
  have -a = -0, by rwa int.neg_zero,
  have a = 0, from int.neg_inj this,
  by contradiction

protected lemma zero_ne_neg_of_ne {a : ℤ} (h : 0 ≠ a) : 0 ≠ -a :=
ne.symm (int.neg_ne_zero_of_ne (ne.symm h))

protected lemma neg_ne_of_pos {a b : ℤ} : 0 < a → 0 < b → -a ≠ b :=
λ h₁ h₂ h,
begin
  rw [← h] at h₂,
  change 0 < a at h₁,
  have := le_of_lt h₁,
  exact absurd (le_of_lt h₁) (not_le_of_gt (int.neg_of_neg_pos h₂))
end

protected lemma ne_neg_of_pos {a b : ℤ} : 0 < a → 0 < b → a ≠ -b :=
λ h₁ h₂, ne.symm (int.neg_ne_of_pos h₂ h₁)

/- 2. Lemmas for proving that positive int numerals are nonneg and positive -/

protected lemma one_pos : 0 < (1:int) :=
int.zero_lt_one

protected lemma bit0_pos {a : ℤ} : 0 < a → 0 < bit0 a :=
λ h, int.add_pos h h

protected lemma bit1_pos {a : ℤ} : 0 ≤ a → 0 < bit1 a :=
λ h, int.lt_add_of_le_of_pos (int.add_nonneg h h) int.zero_lt_one

protected lemma zero_nonneg : 0 ≤ (0 : ℤ) :=
le_refl 0

protected lemma one_nonneg : 0 ≤ (1 : ℤ) :=
le_of_lt (int.zero_lt_one)

protected lemma bit0_nonneg {a : ℤ} : 0 ≤ a → 0 ≤ bit0 a :=
λ h, int.add_nonneg h h

protected lemma bit1_nonneg {a : ℤ} : 0 ≤ a → 0 ≤ bit1 a :=
λ h, le_of_lt (int.bit1_pos h)

protected lemma nonneg_of_pos {a : ℤ} : 0 < a → 0 ≤ a :=
le_of_lt

/- 3. nat_abs auxiliary lemmas -/

lemma neg_succ_of_nat_lt_zero (n : ℕ) : neg_succ_of_nat n < 0 :=
@lt.intro _ _ n (by simp [neg_succ_of_nat_coe, int.coe_nat_succ, int.coe_nat_add, int.coe_nat_one,
  int.add_comm, int.add_left_comm, int.neg_add, int.add_right_neg, int.zero_add])

lemma zero_le_of_nat (n : ℕ) : 0 ≤ of_nat n :=
@le.intro _ _ n (by rw [int.zero_add, int.coe_nat_eq])

lemma of_nat_nat_abs_eq_of_nonneg : ∀ {a : ℤ}, 0 ≤ a → of_nat (nat_abs a) = a
| (of_nat n)          h := rfl
| (neg_succ_of_nat n) h := absurd (neg_succ_of_nat_lt_zero n) (not_lt_of_ge h)

lemma ne_of_nat_abs_ne_nat_abs_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (h : nat_abs a ≠ nat_abs b) : a ≠ b :=
assume h,
  have of_nat (nat_abs a) = of_nat (nat_abs b),
  by rwa [of_nat_nat_abs_eq_of_nonneg ha, of_nat_nat_abs_eq_of_nonneg hb],
  begin injection this, contradiction end

protected lemma ne_of_nat_ne_nonneg_case {a b : ℤ} {n m : nat} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (e1 : nat_abs a = n) (e2 : nat_abs b = m) (h : n ≠ m) : a ≠ b :=
have nat_abs a ≠ nat_abs b, by rwa [e1, e2],
ne_of_nat_abs_ne_nat_abs_of_nonneg ha hb this

/- 4. Aux lemmas for pushing nat_abs inside numerals
   nat_abs_zero and nat_abs_one are defined at init/data/int/basic.lean -/

lemma nat_abs_of_nat_core (n : ℕ) : nat_abs (of_nat n) = n :=
rfl

lemma nat_abs_of_neg_succ_of_nat (n : ℕ) : nat_abs (neg_succ_of_nat n) = nat.succ n :=
rfl

protected lemma nat_abs_add_nonneg :
  ∀ {a b : int}, 0 ≤ a → 0 ≤ b → nat_abs (a + b) = nat_abs a + nat_abs b
| (of_nat n) (of_nat m)  h₁ h₂ :=
  have of_nat n + of_nat m = of_nat (n + m), from rfl,
  by simp [nat_abs_of_nat_core, this]
| _  (neg_succ_of_nat m) h₁ h₂ := absurd (neg_succ_of_nat_lt_zero m) (not_lt_of_ge h₂)
| (neg_succ_of_nat n) _  h₁ h₂ := absurd (neg_succ_of_nat_lt_zero n) (not_lt_of_ge h₁)

protected lemma nat_abs_add_neg :
  ∀ {a b : int}, a < 0 → b < 0 → nat_abs (a + b) = nat_abs a + nat_abs b
| (neg_succ_of_nat n) (neg_succ_of_nat m) h₁ h₂ :=
  have -[1+ n] + -[1+ m] = -[1+ nat.succ (n + m)], from rfl,
  begin simp [nat_abs_of_neg_succ_of_nat, this, nat.succ_add, nat.add_succ] end

protected lemma nat_abs_bit0 : ∀ (a : int), nat_abs (bit0 a) = bit0 (nat_abs a)
| (of_nat n)          := int.nat_abs_add_nonneg (zero_le_of_nat n) (zero_le_of_nat n)
| (neg_succ_of_nat n) := int.nat_abs_add_neg (neg_succ_of_nat_lt_zero n) (neg_succ_of_nat_lt_zero n)

protected lemma nat_abs_bit0_step {a : int} {n : nat} (h : nat_abs a = n) :
  nat_abs (bit0 a) = bit0 n :=
begin rw [← h], apply int.nat_abs_bit0 end

protected lemma nat_abs_bit1_nonneg {a : int} (h : 0 ≤ a) : nat_abs (bit1 a) = bit1 (nat_abs a) :=
show nat_abs (bit0 a + 1) = bit0 (nat_abs a) + nat_abs 1, from
by rw [int.nat_abs_add_nonneg (int.bit0_nonneg h) (le_of_lt (int.zero_lt_one)), int.nat_abs_bit0]

protected lemma nat_abs_bit1_nonneg_step {a : int} {n : nat} (h₁ : 0 ≤ a) (h₂ : nat_abs a = n) :
  nat_abs (bit1 a) = bit1 n :=
begin rw [← h₂], apply int.nat_abs_bit1_nonneg h₁ end

end int
