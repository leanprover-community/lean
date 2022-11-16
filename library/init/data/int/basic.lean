/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
prelude
import init.data.nat.lemmas init.data.nat.gcd
open nat

/-!
# The integers, with addition, multiplication, and subtraction.

the type, coercions, and notation -/

@[derive decidable_eq]
inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int

notation `ℤ` := int

instance : has_coe nat int := ⟨int.of_nat⟩

notation `-[1+ ` n `]` := int.neg_succ_of_nat n

protected def int.repr : int → string
| (int.of_nat n)          := repr n
| (int.neg_succ_of_nat n) := "-" ++ repr (succ n)

instance : has_repr int :=
⟨int.repr⟩

instance : has_to_string int :=
⟨int.repr⟩

namespace int

protected lemma coe_nat_eq (n : ℕ) : ↑n = int.of_nat n := rfl

protected def zero : ℤ := of_nat 0
protected def one  : ℤ := of_nat 1

instance : has_zero ℤ := ⟨int.zero⟩
instance : has_one ℤ := ⟨int.one⟩

lemma of_nat_zero : of_nat (0 : nat) = (0 : int) := rfl

lemma of_nat_one : of_nat (1 : nat) = (1 : int) := rfl

/-! definitions of basic functions -/

def neg_of_nat : ℕ → ℤ
| 0        := 0
| (succ m) := -[1+ m]

def sub_nat_nat (m n : ℕ) : ℤ :=
match (n - m : nat) with
| 0        := of_nat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k
end

lemma sub_nat_nat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) :
  sub_nat_nat m n = of_nat (m - n) :=
begin unfold sub_nat_nat, rw h, unfold sub_nat_nat._match_1 end

lemma sub_nat_nat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) :
  sub_nat_nat m n = -[1+ k] :=
begin unfold sub_nat_nat, rw h, unfold sub_nat_nat._match_1 end

protected def neg : ℤ → ℤ
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

protected def add : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m + n)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m]    -[1+ n]    := -[1+ succ (m + n)]

protected def mul : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m]    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m]    -[1+ n]    := of_nat (succ m * succ n)

instance : has_neg ℤ := ⟨int.neg⟩
instance : has_add ℤ := ⟨int.add⟩
instance : has_mul ℤ := ⟨int.mul⟩

-- defeq to algebra.sub which gives subtraction for arbitrary `add_group`s
protected def sub : ℤ → ℤ → ℤ :=
λ m n, m + -n

instance : has_sub ℤ := ⟨int.sub⟩

protected lemma neg_zero : -(0:ℤ) = 0 := rfl

lemma of_nat_add (n m : ℕ) : of_nat (n + m) = of_nat n + of_nat m := rfl
lemma of_nat_mul (n m : ℕ) : of_nat (n * m) = of_nat n * of_nat m := rfl
lemma of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1 := rfl

lemma neg_of_nat_zero : -(of_nat 0) = 0 := rfl
lemma neg_of_nat_of_succ (n : ℕ) : -(of_nat (succ n)) = -[1+ n] := rfl
lemma neg_neg_of_nat_succ (n : ℕ) : -(-[1+ n]) = of_nat (succ n) := rfl

lemma of_nat_eq_coe (n : ℕ) : of_nat n = ↑n := rfl
lemma neg_succ_of_nat_coe (n : ℕ) : -[1+ n] = -↑(n + 1) := rfl

protected lemma coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n := rfl
protected lemma coe_nat_mul (m n : ℕ) : (↑(m * n) : ℤ) = ↑m * ↑n := rfl
protected lemma coe_nat_zero : ↑(0 : ℕ) = (0 : ℤ) := rfl
protected lemma coe_nat_one : ↑(1 : ℕ) = (1 : ℤ) := rfl
protected lemma coe_nat_succ (n : ℕ) : (↑(succ n) : ℤ) = ↑n + 1 := rfl

protected lemma coe_nat_add_out (m n : ℕ) : ↑m + ↑n = (m + n : ℤ) := rfl
protected lemma coe_nat_mul_out (m n : ℕ) : ↑m * ↑n = (↑(m * n) : ℤ) := rfl
protected lemma coe_nat_add_one_out (n : ℕ) : ↑n + (1 : ℤ) = ↑(succ n) := rfl

/-! these are only for internal use -/

lemma of_nat_add_of_nat (m n : nat) : of_nat m + of_nat n = of_nat (m + n) := rfl
lemma of_nat_add_neg_succ_of_nat (m n : nat) :
                of_nat m + -[1+ n] = sub_nat_nat m (succ n) := rfl
lemma neg_succ_of_nat_add_of_nat (m n : nat) :
                -[1+ m] + of_nat n = sub_nat_nat n (succ m) := rfl
lemma neg_succ_of_nat_add_neg_succ_of_nat (m n : nat) :
                -[1+ m] + -[1+ n] = -[1+ succ (m + n)] := rfl

lemma of_nat_mul_of_nat (m n : nat) : of_nat m * of_nat n = of_nat (m * n) := rfl
lemma of_nat_mul_neg_succ_of_nat (m n : nat) :
                of_nat m * -[1+ n] = neg_of_nat (m * succ n) := rfl
lemma neg_succ_of_nat_of_nat (m n : nat) :
                -[1+ m] * of_nat n = neg_of_nat (succ m * n) := rfl
lemma mul_neg_succ_of_nat_neg_succ_of_nat (m n : nat) :
               -[1+ m] * -[1+ n] = of_nat (succ m * succ n) := rfl

local attribute [simp] of_nat_add_of_nat of_nat_mul_of_nat neg_of_nat_zero neg_of_nat_of_succ
  neg_neg_of_nat_succ of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat
  neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat
  mul_neg_succ_of_nat_neg_succ_of_nat

/-!  some basic functions and properties -/

protected lemma coe_nat_inj {m n : ℕ} (h : (↑m : ℤ) = ↑n) : m = n :=
int.of_nat.inj h

lemma of_nat_eq_of_nat_iff (m n : ℕ) : of_nat m = of_nat n ↔ m = n :=
iff.intro int.of_nat.inj (congr_arg _)

protected lemma coe_nat_eq_coe_nat_iff (m n : ℕ) : (↑m : ℤ) = ↑n ↔ m = n :=
of_nat_eq_of_nat_iff m n

lemma neg_succ_of_nat_inj_iff {m n : ℕ} : neg_succ_of_nat m = neg_succ_of_nat n ↔ m = n :=
⟨neg_succ_of_nat.inj, assume H, by simp [H]⟩

lemma neg_succ_of_nat_eq (n : ℕ) : -[1+ n] = -(n + 1) := rfl

/-! neg -/

protected lemma neg_neg : ∀ a : ℤ, -(-a) = a
| (of_nat 0)     := rfl
| (of_nat (n+1)) := rfl
| -[1+ n]        := rfl

protected lemma neg_inj {a b : ℤ} (h : -a = -b) : a = b :=
by rw [← int.neg_neg a, ← int.neg_neg b, h]

protected lemma sub_eq_add_neg {a b : ℤ} : a - b = a + -b := rfl

/-! basic properties of sub_nat_nat -/

lemma sub_nat_nat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop)
  (hp : ∀i n, P (n + i) n (of_nat i))
  (hn : ∀i m, P m (m + i + 1) (-[1+ i])) :
  P m n (sub_nat_nat m n) :=
begin
  have H : ∀k, n - m = k → P m n (nat.cases_on k (of_nat (m - n)) (λa, -[1+ a])),
  { intro k, cases k,
    { intro e,
      cases (nat.le.dest (nat.le_of_sub_eq_zero e)) with k h,
      rw [h.symm, nat.add_sub_cancel_left],
      apply hp },
    { intro heq,
      have h : m ≤ n,
      { exact nat.le_of_lt (nat.lt_of_sub_eq_succ heq) },
      rw [nat.sub_eq_iff_eq_add h] at heq,
      rw [heq, nat.add_comm],
      apply hn } },
  delta sub_nat_nat,
  exact H _ rfl
end

lemma sub_nat_nat_add_left {m n : ℕ} :
  sub_nat_nat (m + n) m = of_nat n :=
begin
  dunfold sub_nat_nat,
  rw [nat.sub_eq_zero_of_le],
  dunfold sub_nat_nat._match_1,
  rw [nat.add_sub_cancel_left],
  apply nat.le_add_right
end

lemma sub_nat_nat_add_right {m n : ℕ} :
  sub_nat_nat m (m + n + 1) = neg_succ_of_nat n :=
calc sub_nat_nat._match_1 m (m + n + 1) (m + n + 1 - m) =
        sub_nat_nat._match_1 m (m + n + 1) (m + (n + 1) - m) : by rw [nat.add_assoc]
  ... = sub_nat_nat._match_1 m (m + n + 1) (n + 1) : by rw [nat.add_sub_cancel_left]
  ... = neg_succ_of_nat n : rfl

lemma sub_nat_nat_add_add (m n k : ℕ) : sub_nat_nat (m + k) (n + k) = sub_nat_nat m n :=
sub_nat_nat_elim m n (λm n i, sub_nat_nat (m + k) (n + k) = i)
  (assume i n, have n + i + k = (n + k) + i, by simp [nat.add_comm, nat.add_left_comm],
    begin rw [this], exact sub_nat_nat_add_left end)
  (assume i m, have m + i + 1 + k = (m + k) + i + 1, by simp [nat.add_comm, nat.add_left_comm],
    begin rw [this], exact sub_nat_nat_add_right end)

lemma sub_nat_nat_of_le {m n : ℕ} (h : n ≤ m) : sub_nat_nat m n = of_nat (m - n) :=
sub_nat_nat_of_sub_eq_zero (nat.sub_eq_zero_of_le h)

lemma sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : sub_nat_nat m n = -[1+ pred (n - m)] :=
have n - m = succ (pred (n - m)), from eq.symm (succ_pred_eq_of_pos (nat.sub_pos_of_lt h)),
by rewrite sub_nat_nat_of_sub_eq_succ this

/-! nat_abs -/

@[simp] def nat_abs : ℤ → ℕ
| (of_nat m) := m
| -[1+ m]    := succ m

lemma nat_abs_of_nat (n : ℕ) : nat_abs ↑n = n := rfl

lemma eq_zero_of_nat_abs_eq_zero : Π {a : ℤ}, nat_abs a = 0 → a = 0
| (of_nat m) H := congr_arg of_nat H
| -[1+ m']   H := absurd H (succ_ne_zero _)

lemma nat_abs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : 0 < nat_abs a :=
(nat.eq_zero_or_pos _).resolve_left $ mt eq_zero_of_nat_abs_eq_zero h

lemma nat_abs_zero : nat_abs (0 : int) = (0 : nat) := rfl

lemma nat_abs_one : nat_abs (1 : int) = (1 : nat) := rfl

lemma nat_abs_mul_self : Π {a : ℤ}, ↑(nat_abs a * nat_abs a) = a * a
| (of_nat m) := rfl
| -[1+ m']   := rfl

@[simp] lemma nat_abs_neg (a : ℤ) : nat_abs (-a) = nat_abs a :=
by {cases a with n n, cases n; refl, refl}

lemma nat_abs_eq : Π (a : ℤ), a = nat_abs a ∨ a = -(nat_abs a)
| (of_nat m) := or.inl rfl
| -[1+ m']   := or.inr rfl

lemma eq_coe_or_neg (a : ℤ) : ∃n : ℕ, a = n ∨ a = -n := ⟨_, nat_abs_eq a⟩

/-! sign -/

def sign : ℤ → ℤ
| (n+1:ℕ) := 1
| 0       := 0
| -[1+ n] := -1

@[simp] theorem sign_zero : sign 0 = 0 := rfl
@[simp] theorem sign_one : sign 1 = 1 := rfl
@[simp] theorem sign_neg_one : sign (-1) = -1 := rfl

/-! Quotient and remainder -/

-- There are three main conventions for integer division,
-- referred here as the E, F, T rounding conventions.
-- All three pairs satisfy the identity x % y + (x / y) * y = x
-- unconditionally.

-- E-rounding: This pair satisfies 0 ≤ mod x y < nat_abs y for y ≠ 0
protected def div : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m : ℕ) -[1+ n] := -of_nat (m / succ n)
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ (m / succ n))

protected def mod : ℤ → ℤ → ℤ
| (m : ℕ) n := (m % nat_abs n : ℕ)
| -[1+ m] n := sub_nat_nat (nat_abs n) (succ (m % nat_abs n))

-- F-rounding: This pair satisfies fdiv x y = floor (x / y)
def fdiv : ℤ → ℤ → ℤ
| 0       _       := 0
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m+1:ℕ) -[1+ n] := -[1+ m / succ n]
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ m / succ n)

def fmod : ℤ → ℤ → ℤ
| 0       _       := 0
| (m : ℕ) (n : ℕ) := of_nat (m % n)
| (m+1:ℕ) -[1+ n] := sub_nat_nat (m % succ n) n
| -[1+ m] (n : ℕ) := sub_nat_nat n (succ (m % n))
| -[1+ m] -[1+ n] := -of_nat (succ m % succ n)

-- T-rounding: This pair satisfies quot x y = round_to_zero (x / y)
def quot : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m / n)
| (of_nat m) -[1+ n]    := -of_nat (m / succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m / n)
| -[1+ m]    -[1+ n]    := of_nat (succ m / succ n)

def rem : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m % n)
| (of_nat m) -[1+ n]    := of_nat (m % succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m % n)
| -[1+ m]    -[1+ n]    := -of_nat (succ m % succ n)

instance : has_div ℤ := ⟨int.div⟩
instance : has_mod ℤ := ⟨int.mod⟩

/-! gcd -/

def gcd (m n : ℤ) : ℕ := gcd (nat_abs m) (nat_abs n)

/-
   int is a ring
-/

/-! addition -/

protected lemma add_comm : ∀ a b : ℤ, a + b = b + a
| (of_nat n) (of_nat m) := by simp [nat.add_comm]
| (of_nat n) -[1+ m]    := rfl
| -[1+ n]    (of_nat m) := rfl
| -[1+ n]    -[1+m]     := by simp [nat.add_comm]

protected lemma add_zero : ∀ a : ℤ, a + 0 = a
| (of_nat n) := rfl
| -[1+ n]   := rfl

protected lemma zero_add (a : ℤ) : 0 + a = a :=
int.add_comm a 0 ▸ int.add_zero a

lemma sub_nat_nat_sub {m n : ℕ} (h : n ≤ m) (k : ℕ) :
  sub_nat_nat (m - n) k = sub_nat_nat m (k + n) :=
calc
  sub_nat_nat (m - n) k = sub_nat_nat (m - n + n) (k + n) : by rewrite [sub_nat_nat_add_add]
                    ... = sub_nat_nat m (k + n)           : by rewrite [nat.sub_add_cancel h]

lemma sub_nat_nat_add (m n k : ℕ) : sub_nat_nat (m + n) k = of_nat m + sub_nat_nat n k :=
begin
  have h := le_or_lt k n,
  cases h with h' h',
  { rw [sub_nat_nat_of_le h'],
    have h₂ : k ≤ m + n, exact (le_trans h' (nat.le_add_left _ _)),
    rw [sub_nat_nat_of_le h₂], simp,
    rw nat.add_sub_assoc h' },
  rw [sub_nat_nat_of_lt h'], simp, rw [succ_pred_eq_of_pos (nat.sub_pos_of_lt h')],
  transitivity, rw [← nat.sub_add_cancel (le_of_lt h')],
  apply sub_nat_nat_add_add
end

lemma sub_nat_nat_add_neg_succ_of_nat (m n k : ℕ) :
    sub_nat_nat m n + -[1+ k] = sub_nat_nat m (n + succ k) :=
begin
  have h := le_or_lt n m,
  cases h with h' h',
  { rw [sub_nat_nat_of_le h'], simp, rw [sub_nat_nat_sub h', nat.add_comm] },
  have h₂ : m < n + succ k, exact nat.lt_of_lt_of_le h' (nat.le_add_right _ _),
  have h₃ : m ≤ n + k, exact le_of_succ_le_succ h₂,
  rw [sub_nat_nat_of_lt h', sub_nat_nat_of_lt h₂], simp [nat.add_comm],
  rw [← add_succ, succ_pred_eq_of_pos (nat.sub_pos_of_lt h'), add_succ, succ_sub h₃, pred_succ],
  rw [nat.add_comm n, nat.add_sub_assoc (le_of_lt h')]
end

lemma add_assoc_aux1 (m n : ℕ) :
    ∀ c : ℤ, of_nat m + of_nat n + c = of_nat m + (of_nat n + c)
| (of_nat k) := by simp [nat.add_assoc]
| -[1+ k]    := by simp [sub_nat_nat_add]

lemma add_assoc_aux2 (m n k : ℕ) :
  -[1+ m] + -[1+ n] + of_nat k = -[1+ m] + (-[1+ n] + of_nat k) :=
begin
  simp [add_succ], rw [int.add_comm, sub_nat_nat_add_neg_succ_of_nat], simp [add_succ, succ_add, nat.add_comm]
end

protected lemma add_assoc : ∀ a b c : ℤ, a + b + c = a + (b + c)
| (of_nat m) (of_nat n) c          := add_assoc_aux1 _ _ _
| (of_nat m) b          (of_nat k) := by rw [int.add_comm, ← add_assoc_aux1, int.add_comm (of_nat k),
                                         add_assoc_aux1, int.add_comm b]
| a          (of_nat n) (of_nat k) := by rw [int.add_comm, int.add_comm a, ← add_assoc_aux1,
                                         int.add_comm a, int.add_comm (of_nat k)]
| -[1+ m]    -[1+ n]    (of_nat k) := add_assoc_aux2 _ _ _
| -[1+ m]    (of_nat n) -[1+ k]    := by rw [int.add_comm, ← add_assoc_aux2, int.add_comm (of_nat n),
                                         ← add_assoc_aux2, int.add_comm -[1+ m] ]
| (of_nat m) -[1+ n]    -[1+ k]    := by rw [int.add_comm, int.add_comm (of_nat m),
                                         int.add_comm (of_nat m), ← add_assoc_aux2,
                                         int.add_comm -[1+ k] ]
| -[1+ m]    -[1+ n]    -[1+ k]    := by simp [add_succ, nat.add_comm, nat.add_left_comm, neg_of_nat_of_succ]

/-! negation -/

lemma sub_nat_self : ∀ n, sub_nat_nat n n = 0
| 0        := rfl
| (succ m) := begin rw [sub_nat_nat_of_sub_eq_zero, nat.sub_self, of_nat_zero], rw nat.sub_self end

local attribute [simp] sub_nat_self

protected lemma add_left_neg : ∀ a : ℤ, -a + a = 0
| (of_nat 0)        := rfl
| (of_nat (succ m)) := by simp
| -[1+ m]           := by simp

protected lemma add_right_neg (a : ℤ) : a + -a = 0 :=
by rw [int.add_comm, int.add_left_neg]

/-! multiplication -/

protected lemma mul_comm : ∀ a b : ℤ, a * b = b * a
| (of_nat m) (of_nat n) := by simp [nat.mul_comm]
| (of_nat m) -[1+ n]    := by simp [nat.mul_comm]
| -[1+ m]    (of_nat n) := by simp [nat.mul_comm]
| -[1+ m]    -[1+ n]    := by simp [nat.mul_comm]

lemma of_nat_mul_neg_of_nat (m : ℕ) :
   ∀ n, of_nat m * neg_of_nat n = neg_of_nat (m * n)
| 0        := rfl
| (succ n) := begin unfold neg_of_nat, simp end

lemma neg_of_nat_mul_of_nat (m n : ℕ) :
    neg_of_nat m * of_nat n = neg_of_nat (m * n) :=
begin rw int.mul_comm, simp [of_nat_mul_neg_of_nat, nat.mul_comm] end

lemma neg_succ_of_nat_mul_neg_of_nat (m : ℕ) :
  ∀ n, -[1+ m] * neg_of_nat n = of_nat (succ m * n)
| 0        := rfl
| (succ n) := begin unfold neg_of_nat, simp end

lemma neg_of_nat_mul_neg_succ_of_nat (m n : ℕ) :
  neg_of_nat n * -[1+ m] = of_nat (n * succ m) :=
begin rw int.mul_comm, simp [neg_succ_of_nat_mul_neg_of_nat, nat.mul_comm] end

local attribute [simp] of_nat_mul_neg_of_nat neg_of_nat_mul_of_nat
  neg_succ_of_nat_mul_neg_of_nat neg_of_nat_mul_neg_succ_of_nat

protected lemma mul_assoc : ∀ a b c : ℤ, a * b * c = a * (b * c)
| (of_nat m) (of_nat n) (of_nat k) := by simp [nat.mul_assoc]
| (of_nat m) (of_nat n) -[1+ k]    := by simp [nat.mul_assoc]
| (of_nat m) -[1+ n]    (of_nat k) := by simp [nat.mul_assoc]
| (of_nat m) -[1+ n]   -[1+ k]     := by simp [nat.mul_assoc]
| -[1+ m]    (of_nat n) (of_nat k) := by simp [nat.mul_assoc]
| -[1+ m]    (of_nat n) -[1+ k]    := by simp [nat.mul_assoc]
| -[1+ m]    -[1+ n]    (of_nat k) := by simp [nat.mul_assoc]
| -[1+ m]    -[1+ n]   -[1+ k]     := by simp [nat.mul_assoc]

protected lemma mul_zero : ∀ (a : ℤ), a * 0 = 0
| (of_nat m) := rfl
| -[1+ m]    := rfl

protected lemma zero_mul (a : ℤ) : 0 * a = 0 :=
int.mul_comm a 0 ▸ int.mul_zero a

lemma neg_of_nat_eq_sub_nat_nat_zero : ∀ n, neg_of_nat n = sub_nat_nat 0 n
| 0        := rfl
| (succ n) := rfl

lemma of_nat_mul_sub_nat_nat (m n k : ℕ) :
  of_nat m * sub_nat_nat n k = sub_nat_nat (m * n) (m * k) :=
begin
  have h₀ : m > 0 ∨ 0 = m,
    exact decidable.lt_or_eq_of_le m.zero_le,
  cases h₀ with h₀ h₀,
  { have h := nat.lt_or_ge n k,
    cases h with h h,
    { have h' : m * n < m * k,
        exact nat.mul_lt_mul_of_pos_left h h₀,
      rw [sub_nat_nat_of_lt h, sub_nat_nat_of_lt h'],
      simp, rw [succ_pred_eq_of_pos (nat.sub_pos_of_lt h)],
      rw [← neg_of_nat_of_succ, nat.mul_sub_left_distrib],
      rw [← succ_pred_eq_of_pos (nat.sub_pos_of_lt h')], reflexivity },
    have h' : m * k ≤ m * n,
      exact nat.mul_le_mul_left _ h,
    rw [sub_nat_nat_of_le h, sub_nat_nat_of_le h'], simp,
    rw [nat.mul_sub_left_distrib]
  },
  have h₂ : of_nat 0 = 0, exact rfl,
  subst h₀, simp [h₂, int.zero_mul, nat.zero_mul]
end

lemma neg_of_nat_add (m n : ℕ) :
  neg_of_nat m + neg_of_nat n = neg_of_nat (m + n) :=
begin
  cases m,
  {  cases n,
    { simp, reflexivity },
      simp [nat.zero_add], reflexivity },
  cases n,
  { simp, reflexivity },
  simp [nat.succ_add], reflexivity
end

lemma neg_succ_of_nat_mul_sub_nat_nat (m n k : ℕ) :
  -[1+ m] * sub_nat_nat n k = sub_nat_nat (succ m * k) (succ m * n) :=
begin
  have h := nat.lt_or_ge n k,
  cases h with h h,
  { have h' : succ m * n < succ m * k,
      exact nat.mul_lt_mul_of_pos_left h (nat.succ_pos m),
    rw [sub_nat_nat_of_lt h, sub_nat_nat_of_le (le_of_lt h')],
    simp [succ_pred_eq_of_pos (nat.sub_pos_of_lt h), nat.mul_sub_left_distrib]},
  have h' : n > k ∨ k = n,
    exact decidable.lt_or_eq_of_le h,
  cases h' with h' h',
  { have h₁ : succ m * n > succ m * k,
      exact nat.mul_lt_mul_of_pos_left h' (nat.succ_pos m),
    rw [sub_nat_nat_of_le h, sub_nat_nat_of_lt h₁], simp [nat.mul_sub_left_distrib, nat.mul_comm],
    rw [nat.mul_comm k, nat.mul_comm n, ← succ_pred_eq_of_pos (nat.sub_pos_of_lt h₁),
        ← neg_of_nat_of_succ],
    reflexivity },
  subst h', simp, reflexivity
end

local attribute [simp] of_nat_mul_sub_nat_nat neg_of_nat_add neg_succ_of_nat_mul_sub_nat_nat

protected lemma distrib_left : ∀ a b c : ℤ, a * (b + c) = a * b + a * c
| (of_nat m) (of_nat n) (of_nat k) := by simp [nat.left_distrib]
| (of_nat m) (of_nat n) -[1+ k]    := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw ← sub_nat_nat_add, reflexivity end
| (of_nat m) -[1+ n]    (of_nat k) := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [int.add_comm, ← sub_nat_nat_add], reflexivity end
| (of_nat m) -[1+ n]   -[1+ k]     := begin simp, rw [← nat.left_distrib, add_succ, succ_add] end
| -[1+ m]    (of_nat n) (of_nat k) := begin simp [nat.mul_comm], rw [← nat.right_distrib, nat.mul_comm] end
| -[1+ m]    (of_nat n) -[1+ k]    := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [int.add_comm, ← sub_nat_nat_add], reflexivity end
| -[1+ m]    -[1+ n]    (of_nat k) := begin simp [neg_of_nat_eq_sub_nat_nat_zero],
                                            rw [← sub_nat_nat_add], reflexivity end
| -[1+ m]    -[1+ n]   -[1+ k]     := begin simp, rw [← nat.left_distrib, add_succ, succ_add] end

protected lemma distrib_right (a b c : ℤ) : (a + b) * c = a * c + b * c :=
begin rw [int.mul_comm, int.distrib_left], simp [int.mul_comm] end

protected lemma zero_ne_one : (0 : int) ≠ 1 :=
assume h : 0 = 1, succ_ne_zero _ (int.of_nat.inj h).symm

lemma of_nat_sub {n m : ℕ} (h : m ≤ n) : of_nat (n - m) = of_nat n - of_nat m :=
show of_nat (n - m) = of_nat n + neg_of_nat m, from match m, h with
| 0, h := rfl
| succ m, h := show of_nat (n - succ m) = sub_nat_nat n (succ m),
  by delta sub_nat_nat; rw nat.sub_eq_zero_of_le h; refl
end

protected lemma add_left_comm (a b c : ℤ) : a + (b + c) = b + (a + c) :=
by rw [← int.add_assoc, int.add_comm a, int.add_assoc]

protected lemma add_left_cancel {a b c : ℤ} (h : a + b = a + c) : b = c :=
have -a + (a + b) = -a + (a + c), by rw h,
by rwa [← int.add_assoc, ← int.add_assoc, int.add_left_neg, int.zero_add, int.zero_add] at this

protected lemma neg_add {a b : ℤ} : - (a + b) = -a + -b :=
calc - (a + b) = -(a + b) + (a + b) + -a + -b :
begin
  rw [int.add_assoc, int.add_comm (-a), int.add_assoc, int.add_assoc, ← int.add_assoc b],
  rw [int.add_right_neg, int.zero_add, int.add_right_neg, int.add_zero],
end
  ... = -a + -b : by { rw [int.add_left_neg, int.zero_add] }

lemma neg_succ_of_nat_coe' (n : ℕ) : -[1+ n] = -↑n - 1 :=
by rw [int.sub_eq_add_neg, ← int.neg_add]; refl

protected lemma coe_nat_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := of_nat_sub

local attribute [simp] int.sub_eq_add_neg

protected lemma sub_nat_nat_eq_coe {m n : ℕ} : sub_nat_nat m n = ↑m - ↑n :=
sub_nat_nat_elim m n (λm n i, i = ↑m - ↑n)
  (λi n, by { simp [int.coe_nat_add, int.add_left_comm, int.add_assoc, int.add_right_neg], refl })
  (λi n, by { rw [int.coe_nat_add, int.coe_nat_add, int.coe_nat_one, int.neg_succ_of_nat_eq,
                  int.sub_eq_add_neg, int.neg_add, int.neg_add, int.neg_add, ← int.add_assoc,
                  ← int.add_assoc, int.add_right_neg, int.zero_add] })

def to_nat : ℤ → ℕ
| (n : ℕ) := n
| -[1+ n] := 0

theorem to_nat_sub (m n : ℕ) : to_nat (m - n) = m - n :=
by rw [← int.sub_nat_nat_eq_coe]; exact sub_nat_nat_elim m n
  (λm n i, to_nat i = m - n)
  (λi n, by rw [nat.add_sub_cancel_left]; refl)
  (λi n, by rw [nat.add_assoc, nat.sub_eq_zero_of_le (nat.le_add_right _ _)]; refl)

-- Since mod x y is always nonnegative when y ≠ 0, we can make a nat version of it
def nat_mod (m n : ℤ) : ℕ := (m % n).to_nat

protected lemma one_mul : ∀ (a : ℤ), (1 : ℤ) * a = a
| (of_nat n) := show of_nat (1 * n) = of_nat n, by rw nat.one_mul
| -[1+ n]    := show -[1+ (1 * n)] = -[1+ n], by rw nat.one_mul

protected lemma mul_one (a : ℤ) : a * 1 = a :=
by rw [int.mul_comm, int.one_mul]

protected lemma neg_eq_neg_one_mul : ∀ a : ℤ, -a = -1 * a
| (of_nat 0)     := rfl
| (of_nat (n+1)) := show _ = -[1+ (1*n)+0], by { rw nat.one_mul, refl }
| -[1+ n]        := show _ = of_nat _, by { rw nat.one_mul, refl }

theorem sign_mul_nat_abs : ∀ (a : ℤ), sign a * nat_abs a = a
| (n+1:ℕ) := int.one_mul _
| 0       := rfl
| -[1+ n] := (int.neg_eq_neg_one_mul _).symm

end int
