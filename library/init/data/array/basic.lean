/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import init.data.nat init.data.bool init.ite_simp
universes u v w

/-- In the VM, d_array is implemented as a persistent array. -/
structure d_array (n : nat) (α : fin n → Type u) :=
(data : Π i : fin n, α i)

namespace d_array
variables {n : nat} {α : fin n → Type u} {α' : fin n → Type v} {β : Type w}

/-- The empty array. -/
def nil {α} : d_array 0 α :=
{data := λ ⟨x, h⟩, absurd h (nat.not_lt_zero x)}

/-- `read a i` reads the `i`th member of `a`. Has builtin VM implementation. -/
def read (a : d_array n α) (i : fin n) : α i :=
a.data i

/-- `write a i v` sets the `i`th member of `a` to be `v`. Has builtin VM implementation. -/
def write (a : d_array n α) (i : fin n) (v : α i) : d_array n α :=
{data := λ j, if h : i = j then eq.rec_on h v else a.read j}

def iterate_aux (a : d_array n α) (f : Π i : fin n, α i → β → β) : Π (i : nat), i ≤ n → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin n := ⟨j, h⟩ in
  f i (a.read i) (iterate_aux j (le_of_lt h) b)

/-- Fold over the elements of the given array in ascending order. Has builtin VM implementation. -/
def iterate (a : d_array n α) (b : β) (f : Π i : fin n, α i → β → β) : β :=
iterate_aux a f n (le_refl _) b

/-- Map the array. Has builtin VM implementation. -/
def foreach (a : d_array n α) (f : Π i : fin n, α i → α' i) : d_array n α' :=
⟨λ i, f _ (a.read i)⟩

def map (f : Π i : fin n, α i → α' i) (a : d_array n α) : d_array n α' :=
foreach a f

def map₂ {α'' : fin n → Type w} (f : Π i : fin n, α i → α' i → α'' i) (a : d_array n α) (b : d_array n α') :
  d_array n α'' :=
foreach b (λ i, f i (a.read i))

def foldl (a : d_array n α) (b : β) (f : Π i : fin n, α i → β → β) : β :=
iterate a b f

def rev_iterate_aux (a : d_array n α) (f : Π i : fin n, α i → β → β) : Π (i : nat), i ≤ n → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin n := ⟨j, h⟩ in
  rev_iterate_aux j (le_of_lt h) (f i (a.read i) b)

def rev_iterate (a : d_array n α) (b : β) (f : Π i : fin n, α i → β → β) : β :=
rev_iterate_aux a f n (le_refl _) b

@[simp] lemma read_write (a : d_array n α) (i : fin n) (v : α i) : read (write a i v) i = v :=
by simp [read, write]

@[simp] lemma read_write_of_ne (a : d_array n α) {i j : fin n} (v : α i) : i ≠ j → read (write a i v) j = read a j :=
by intro h; simp [read, write, h]

protected lemma ext {a b : d_array n α} (h : ∀ i, read a i = read b i) : a = b :=
by cases a; cases b; congr; exact funext h

protected lemma ext' {a b : d_array n α} (h : ∀ (i : nat) (h : i < n), read a ⟨i, h⟩ = read b ⟨i, h⟩) : a = b :=
begin cases a, cases b, congr, funext i, cases i, apply h end

protected def beq_aux [∀ i, decidable_eq (α i)] (a b : d_array n α) : Π (i : nat), i ≤ n → bool
| 0     h := tt
| (i+1) h := if a.read ⟨i, h⟩ = b.read ⟨i, h⟩ then beq_aux i (le_of_lt h) else ff

/-- Boolean element-wise equality check. -/
protected def beq [∀ i, decidable_eq (α i)] (a b : d_array n α) : bool :=
d_array.beq_aux a b n (le_refl _)

lemma of_beq_aux_eq_tt [∀ i, decidable_eq (α i)] {a b : d_array n α} : ∀ (i : nat) (h : i ≤ n), d_array.beq_aux a b i h = tt →
                       ∀ (j : nat) (h' : j < i), a.read ⟨j, lt_of_lt_of_le h' h⟩ = b.read ⟨j, lt_of_lt_of_le h' h⟩
| 0     h₁ h₂ j h₃ := absurd h₃ (nat.not_lt_zero _)
| (i+1) h₁ h₂ j h₃ :=
  begin
    have h₂' : read a ⟨i, h₁⟩ = read b ⟨i, h₁⟩ ∧ d_array.beq_aux a b i _ = tt, {simp [d_array.beq_aux] at h₂, assumption},
    have h₁' : i ≤ n, from le_of_lt h₁,
    have ih  : ∀ (j : nat) (h' : j < i), a.read ⟨j, lt_of_lt_of_le h' h₁'⟩ = b.read ⟨j, lt_of_lt_of_le h' h₁'⟩, from of_beq_aux_eq_tt i h₁' h₂'.2,
    by_cases hji : j = i,
    { subst hji, exact h₂'.1 },
    { have j_lt_i : j < i, from lt_of_le_of_ne (nat.le_of_lt_succ h₃) hji,
      exact ih j j_lt_i }
  end

lemma of_beq_eq_tt [∀ i, decidable_eq (α i)] {a b : d_array n α} : d_array.beq a b = tt → a = b :=
begin
  unfold d_array.beq,
  intro h,
  have : ∀ (j : nat) (h : j < n), a.read ⟨j, h⟩ = b.read ⟨j, h⟩, from
    of_beq_aux_eq_tt n (le_refl _) h,
  apply d_array.ext' this
end

lemma of_beq_aux_eq_ff [∀ i, decidable_eq (α i)] {a b : d_array n α} : ∀ (i : nat) (h : i ≤ n), d_array.beq_aux a b i h = ff →
                       ∃ (j : nat) (h' : j < i), a.read ⟨j, lt_of_lt_of_le h' h⟩ ≠ b.read ⟨j, lt_of_lt_of_le h' h⟩
| 0     h₁ h₂ := begin simp [d_array.beq_aux] at h₂, contradiction end
| (i+1) h₁ h₂ :=
  begin
    have h₂' : read a ⟨i, h₁⟩ ≠ read b ⟨i, h₁⟩ ∨ d_array.beq_aux a b i _ = ff, {simp [d_array.beq_aux] at h₂, assumption},
    cases h₂' with h h,
    { existsi i, existsi (nat.lt_succ_self _), exact h },
    { have h₁' : i ≤ n, from le_of_lt h₁,
      have ih : ∃ (j : nat) (h' : j < i), a.read ⟨j, lt_of_lt_of_le h' h₁'⟩ ≠ b.read ⟨j, lt_of_lt_of_le h' h₁'⟩, from of_beq_aux_eq_ff i h₁' h,
      cases ih with j ih,
      cases ih with h' ih,
      existsi j, existsi (nat.lt_succ_of_lt h'),
      exact ih }
  end

lemma of_beq_eq_ff [∀ i, decidable_eq (α i)] {a b : d_array n α} : d_array.beq a b = ff → a ≠ b :=
begin
  unfold d_array.beq,
  intros h hne,
  have : ∃ (j : nat) (h' : j < n), a.read ⟨j, h'⟩ ≠ b.read ⟨j, h'⟩, from of_beq_aux_eq_ff n (le_refl _) h,
  cases this with j this,
  cases this with h' this,
  subst hne,
  contradiction
end

instance [∀ i, decidable_eq (α i)] : decidable_eq (d_array n α) :=
λ a b, if h : d_array.beq a b = tt then is_true (of_beq_eq_tt h) else is_false (of_beq_eq_ff (eq_ff_of_not_eq_tt h))

end d_array

/-- A non-dependent array (see `d_array`). Implemented in the VM as a persistent array.  -/
def array (n : nat) (α : Type u) : Type u :=
d_array n (λ _, α)

/-- `mk_array n v` creates a new array of length `n` where each element is `v`. Has builtin VM implementation. -/
def mk_array {α} (n) (v : α) : array n α :=
{data := λ _, v}

namespace array
variables {n : nat} {α : Type u} {β : Type v}

def nil {α} : array 0 α :=
d_array.nil

@[inline]
def read (a : array n α) (i : fin n) : α :=
d_array.read a i

@[inline]
def write (a : array n α) (i : fin n) (v : α) : array n α :=
d_array.write a i v

/-- Fold array starting from 0, folder function includes an index argument. -/
@[inline]
def iterate (a : array n α) (b : β) (f : fin n → α → β → β) : β :=
d_array.iterate a b f

/-- Map each element of the given array with an index argument. -/
@[inline]
def foreach (a : array n α) (f : fin n → α → β) : array n β :=
d_array.foreach a f

@[inline]
def map₂ (f : α → α → α) (a b : array n α) : array n α :=
foreach b (λ i, f (a.read i))

@[inline]
def foldl (a : array n α) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

def rev_list (a : array n α) : list α :=
a.foldl [] (::)

def rev_iterate (a : array n α) (b : β) (f : fin n → α → β → β) : β :=
d_array.rev_iterate a b f

def rev_foldl (a : array n α) (b : β) (f : α → β → β) : β :=
rev_iterate a b (λ _, f)

def to_list (a : array n α) : list α :=
a.rev_foldl [] (::)

lemma push_back_idx {j n} (h₁ : j < n + 1) (h₂ : j ≠ n) : j < n :=
nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂

/-- `push_back a v` pushes value `v` to the end of the array. Has builtin VM implementation. -/
def push_back (a : array n α) (v : α) : array (n+1) α :=
{data := λ ⟨j, h₁⟩, if h₂ : j = n then v else a.read ⟨j, push_back_idx h₁ h₂⟩}

lemma pop_back_idx {j n} (h : j < n) : j < n + 1 :=
nat.lt.step h

/-- Discard _last_ element in the array. Has builtin VM implementation. -/
def pop_back (a : array (n+1) α) : array n α :=
{data := λ ⟨j, h⟩, a.read ⟨j, pop_back_idx h⟩}

/-- Auxilliary function for monadically mapping a function over an array. -/
@[inline]
def mmap_core {β : Type v} {m : Type v → Type w} [monad m] (a : array n α) (f : α → m β) :
  ∀ i ≤ n, m (array i β)
| 0 _ := pure d_array.nil
| (i+1) h := do
    bs ← mmap_core i (le_of_lt h),
    b ← f (a.read ⟨i, h⟩),
    pure $ bs.push_back b

/-- Monadically map a function over the array. -/
@[inline]
def mmap {β : Type v} {m} [monad m] (a : array n α) (f : α → m β) : m (array n β) :=
a.mmap_core f _ (le_refl _)

/-- Map a function over the array. -/
@[inline]
def map {β : Type v} (a : array n α) (f : α → β) : array n β :=
a.map (λ _, f)

protected def mem (v : α) (a : array n α) : Prop :=
∃ i : fin n, read a i = v

instance : has_mem α (array n α) := ⟨array.mem⟩

theorem read_mem (a : array n α) (i) : read a i ∈ a :=
exists.intro i rfl

instance [has_repr α] : has_repr (array n α) :=
⟨repr ∘ to_list⟩

meta instance [has_to_format α] : has_to_format (array n α) :=
⟨to_fmt ∘ to_list⟩

meta instance [has_to_tactic_format α] : has_to_tactic_format (array n α) :=
⟨tactic.pp ∘ to_list⟩

@[simp] lemma read_write (a : array n α) (i : fin n) (v : α) : read (write a i v) i = v :=
d_array.read_write a i v

@[simp] lemma read_write_of_ne (a : array n α) {i j : fin n} (v : α) : i ≠ j → read (write a i v) j = read a j :=
d_array.read_write_of_ne a v

def read' [inhabited β] (a : array n β) (i : nat) : β :=
if h : i < n then a.read ⟨i,h⟩ else default

def write' (a : array n α) (i : nat) (v : α) : array n α :=
if h : i < n then a.write ⟨i, h⟩ v else a

lemma read_eq_read' [inhabited α] (a : array n α) {i : nat} (h : i < n) : read a ⟨i, h⟩ = read' a i :=
by simp [read', h]

lemma write_eq_write' (a : array n α) {i : nat} (h : i < n) (v : α) : write a ⟨i, h⟩ v = write' a i v :=
by simp [write', h]

protected lemma ext {a b : array n α} (h : ∀ i, read a i = read b i) : a = b :=
d_array.ext h

protected lemma ext' {a b : array n α} (h : ∀ (i : nat) (h : i < n), read a ⟨i, h⟩ = read b ⟨i, h⟩) : a = b :=
d_array.ext' h

instance [decidable_eq α] : decidable_eq (array n α) :=
begin unfold array, apply_instance end

end array
