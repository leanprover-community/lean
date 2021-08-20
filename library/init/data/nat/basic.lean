/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.logic

notation `ℕ` := nat

namespace nat

protected def ble : ℕ → ℕ → bool
| 0     0     := tt
| 0     (m+1) := tt
| (n+1) 0     := ff
| (n+1) (m+1) := ble n m

protected def le (n m : ℕ) : Prop := nat.ble n m = true

@[reducible] protected def lt (n m : ℕ) := nat.le (succ n) m

instance : has_le ℕ :=
⟨nat.le⟩

instance : has_lt ℕ :=
⟨nat.lt⟩

def pred : ℕ → ℕ
| 0     := 0
| (a+1) := a

protected def sub : ℕ → ℕ → ℕ
| a 0     := a
| a (b+1) := pred (sub a b)

protected def mul : nat → nat → nat
| a 0     := 0
| a (b+1) := (mul a b) + a

instance : has_sub ℕ :=
⟨nat.sub⟩

instance : has_mul ℕ :=
⟨nat.mul⟩

-- defeq to the instance provided by comm_semiring
instance : has_dvd ℕ :=
has_dvd.mk (λ a b, ∃ c, b = a * c)

instance : decidable_eq ℕ
| zero     zero     := is_true rfl
| (succ x) zero     := is_false (λ h, nat.no_confusion h)
| zero     (succ y) := is_false (λ h, nat.no_confusion h)
| (succ x) (succ y) :=
    match decidable_eq x y with
    | is_true xeqy := is_true (xeqy ▸ eq.refl (succ x))
    | is_false xney := is_false (λ h, nat.no_confusion h (λ xeqy, absurd xeqy xney))
    end

def {u} repeat {α : Type u} (f : ℕ → α → α) : ℕ → α → α
| 0         a := a
| (succ n)  a := f n (repeat n a)

instance : inhabited ℕ :=
⟨nat.zero⟩

@[simp] lemma nat_zero_eq_zero : nat.zero = 0 :=
rfl

/- properties of inequality -/

@[refl] protected lemma le_refl : ∀ n : ℕ, n ≤ n
| 0     := rfl
| (n+1) := le_refl n

lemma le_succ : ∀ n : ℕ, n ≤ succ n
| 0     := rfl
| (n+1) := le_succ n

lemma succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
λ h, h

protected lemma zero_le : ∀ (n : ℕ), 0 ≤ n
| 0     := rfl
| (n+1) := rfl

lemma zero_lt_succ (n : ℕ) : 0 < succ n :=
succ_le_succ n.zero_le

lemma succ_pos (n : ℕ) : 0 < succ n := zero_lt_succ n

lemma not_succ_le_zero : ∀ (n : ℕ), succ n ≤ 0 → false
.

protected lemma not_lt_zero (a : ℕ) : ¬ a < 0 := not_succ_le_zero a

lemma pred_le_pred : ∀ {n m : ℕ}, n ≤ m → pred n ≤ pred m
| 0     0     h := rfl
| 0     1     h := rfl
| 0     (m+2) h := rfl
| (n+1) (m+1) h := h

lemma le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
pred_le_pred

instance decidable_le : ∀ a b : ℕ, decidable (a ≤ b)
| 0     b     := is_true b.zero_le
| (a+1) 0     := is_false (not_succ_le_zero a)
| (a+1) (b+1) :=
  match decidable_le a b with
  | is_true h  := is_true (succ_le_succ h)
  | is_false h := is_false (λ a, h (le_of_succ_le_succ a))
  end

instance decidable_lt : ∀ a b : ℕ, decidable (a < b) :=
λ a b, nat.decidable_le (succ a) b

lemma succ_lt_succ {n m : ℕ} : n < m → succ n < succ m :=
λ h, h

protected lemma eq_or_lt_of_le : ∀ {a b : ℕ} (h : a ≤ b), a = b ∨ a < b
| 0     0     h := or.inl rfl
| 0     (b+1) h := or.inr (zero_lt_succ b)
| (a+1) (b+1) h := match @eq_or_lt_of_le a b h with
  | or.inl w := or.inl (congr_arg nat.succ w)
  | or.inr w := or.inr (succ_lt_succ w)
  end

lemma lt_succ_of_le {a b : ℕ} : a ≤ b → a < succ b :=
succ_le_succ

@[simp] lemma succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
nat.rec_on b
  (show succ a - succ zero = a - zero, from (eq.refl (succ a - succ zero)))
  (λ b, congr_arg pred)

lemma not_succ_le_self : ∀ n : ℕ, ¬succ n ≤ n :=
λ n, nat.rec (not_succ_le_zero 0) (λ a b c, b (le_of_succ_le_succ c)) n

protected lemma lt_irrefl (n : ℕ) : ¬n < n :=
not_succ_le_self n

protected lemma le_trans : ∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
| 0     0     0     _ _ := rfl
| 0     0     (k+1) _ _ := rfl
| 0     (m+1) (k+1) _ _ := rfl
| (n+1) (m+1) (k+1) h₁ h₂ := @le_trans n m k h₁ h₂

lemma pred_le : ∀ (n : ℕ), pred n ≤ n
| 0     := rfl
| 1     := rfl
| (n+2) := pred_le (n+1)

protected lemma eq_zero_of_le_zero : ∀ {n : ℕ}, n ≤ 0 → n = 0
| 0 _ := rfl

lemma le_zero_iff {n : ℕ} : n ≤ 0 ↔ n = 0 :=
⟨λ h, nat.eq_zero_of_le_zero h, λ h, h ▸ nat.le_refl n⟩

attribute [irreducible] nat.le

lemma pred_lt : ∀ {n : ℕ}, n ≠ 0 → pred n < n
| 0        h := absurd rfl h
| (succ a) h := lt_succ_of_le (nat.le_refl _)

protected lemma sub_le (a b : ℕ) : a - b ≤ a :=
nat.rec_on b (nat.le_refl (a - 0)) (λ b₁, nat.le_trans (pred_le (a - b₁)))

protected lemma sub_lt : ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
| 0     b     h1 h2 := absurd h1 (nat.lt_irrefl 0)
| (a+1) 0     h1 h2 := absurd h2 (nat.lt_irrefl 0)
| (a+1) (b+1) h1 h2 :=
  eq.symm (succ_sub_succ_eq_sub a b) ▸
    show a - b < succ a, from
    lt_succ_of_le (a.sub_le b)

protected lemma lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k :=
nat.le_trans

/- Basic nat.add lemmas -/
protected lemma zero_add : ∀ n : ℕ, 0 + n = n
| 0     := rfl
| (n+1) := congr_arg succ (zero_add n)

lemma succ_add : ∀ n m : ℕ, (succ n) + m = succ (n + m)
| n 0     := rfl
| n (m+1) := congr_arg succ (succ_add n m)

lemma add_succ (n m : ℕ) : n + succ m = succ (n + m) :=
rfl

protected lemma add_zero (n : ℕ) : n + 0 = n :=
rfl

lemma add_one (n : ℕ) : n + 1 = succ n :=
rfl

lemma succ_eq_add_one (n : ℕ) : succ n = n + 1 :=
rfl

/- Basic lemmas for comparing numerals -/

protected lemma bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
show succ (succ n + n) = succ (succ (n + n)), from
congr_arg succ (succ_add n n)

protected lemma zero_lt_bit0 : ∀ {n : nat}, n ≠ 0 → 0 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  calc 0 < succ (succ (bit0 n)) : zero_lt_succ _
     ... = bit0 (succ n)        : (nat.bit0_succ_eq n).symm

protected lemma zero_lt_bit1 (n : nat) : 0 < bit1 n :=
zero_lt_succ _

protected lemma bit0_ne_zero : ∀ {n : ℕ}, n ≠ 0 → bit0 n ≠ 0
| 0     h := absurd rfl h
| (n+1) h :=
  suffices (n+1) + (n+1) ≠ 0, from this,
  suffices succ ((n+1) + n) ≠ 0, from this,
  λ h, nat.no_confusion h

protected lemma bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
show succ (n + n) ≠ 0, from
λ h, nat.no_confusion h

end nat
