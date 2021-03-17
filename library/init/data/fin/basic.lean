/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.nat.basic
import init.propext
open nat

/-- `fin n` is the subtype of `ℕ` consisting of natural numbers strictly smaller than `n`. -/
def fin (n : ℕ) := {i : ℕ // i < n}

namespace fin

/-- Backwards-compatible constructor for `fin n`. -/
def mk {n : ℕ} (i) (h) : fin n := ⟨i, h⟩

protected def lt {n} (a b : fin n) : Prop :=
a.val < b.val

protected def le {n} (a b : fin n) : Prop :=
a.val ≤ b.val

instance {n} : has_lt (fin n)  := ⟨fin.lt⟩
instance {n} : has_le (fin n)  := ⟨fin.le⟩

instance decidable_lt {n} (a b : fin n) :  decidable (a < b) :=
nat.decidable_lt _ _

instance decidable_le {n} (a b : fin n) : decidable (a ≤ b) :=
nat.decidable_le _ _

def {u} elim0 {α : fin 0 → Sort u} : Π (x : fin 0), α x
| ⟨_, h⟩ := absurd h (not_lt_zero _)

variable {n : nat}

lemma eq_of_veq : ∀ {i j : fin n}, i.val = j.val → i = j
| ⟨iv, ilt₁⟩ ⟨.(iv), ilt₂⟩ rfl := rfl

lemma veq_of_eq : ∀ {i j : fin n}, i = j → i.val = j.val
| ⟨iv, ilt⟩ .(_) rfl := rfl

lemma ne_of_vne {i j : fin n} (h : i.val ≠ j.val) : i ≠ j :=
λ h', absurd (veq_of_eq h') h

lemma vne_of_ne {i j : fin n} (h : i ≠ j) : i.val ≠ j.val :=
λ h', absurd (eq_of_veq h') h

end fin

open fin

instance (n : nat) : decidable_eq (fin n) :=
λ i j, decidable_of_decidable_of_iff
  (nat.decidable_eq i.val j.val) ⟨eq_of_veq, veq_of_eq⟩
