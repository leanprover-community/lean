/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/
prelude
import init.data.int.basic init.data.ordering.basic

-- local attribute [simp] sub_eq_add_neg

namespace int

private def nonneg (a : ℤ) : Prop := int.cases_on a (assume n, true) (assume n, false)

protected def le (a b : ℤ) : Prop := nonneg (b - a)

instance : has_le int := ⟨int.le⟩

protected def lt (a b : ℤ) : Prop := (a + 1) ≤ b

instance : has_lt int := ⟨int.lt⟩

private def decidable_nonneg (a : ℤ) : decidable (nonneg a) :=
int.cases_on a (assume a, decidable.true) (assume a, decidable.false)

instance decidable_le (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _

instance decidable_lt (a b : ℤ) : decidable (a < b) := decidable_nonneg _

lemma lt_iff_add_one_le (a b : ℤ) : a < b ↔ a + 1 ≤ b := iff.refl _

private lemma nonneg.elim {a : ℤ} : nonneg a → ∃ n : ℕ, a = n :=
int.cases_on a (assume n H, exists.intro n rfl) (assume n', false.elim)

private lemma nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
int.cases_on a (assume n, or.inl trivial) (assume n, or.inr trivial)

lemma le.intro_sub {a b : ℤ} {n : ℕ} (h : b - a = n) : a ≤ b :=
show nonneg (b - a), by rw h; trivial

end int