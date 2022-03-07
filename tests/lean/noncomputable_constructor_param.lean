inductive A {α : Type*} (x : α)
| c1 (x y z : ℕ) : A
| c2 : A
| c3 (x : ℕ) : A

def foo0 (h : ∃ (x : ℕ), x = x) : A (classical.some h) := A.c2

def foo1 (h : ∃ (x : ℕ), x = x) : A (classical.some h) := A.c3 4

def foo3 (h : ∃ (x : ℕ), x = x) : A (classical.some h) := A.c1 1 2 3

noncomputable
def foo4 (h : ∃ (x : ℕ), x = x) : A (classical.some h) := A.c3 (classical.some h)

noncomputable
def foo5 (h : ∃ (x : ℕ), x = x) : A (classical.some h) := A.c1 1 (classical.some h) 3

class computable {α : Type*} (x : α) :=
(compute : α)
(compute_eq : compute = x)

export computable

attribute [inline] compute

instance {α : Type*} (x : α) (h : ∃ (y : α), y = x) : computable (classical.some h) :=
⟨x, (classical.some_spec h).symm⟩

def foo6 (h : ∃ (n : ℕ), n = 37) := compute (classical.some h)

noncomputable
def foo7 (h : ∃ (n : ℕ), n = 37) := classical.some h

inductive B (α : Type*)
| c (x : α) : B

noncomputable
def foo8 (h : ∃ (n : ℕ), n = 37) := B.c (classical.some h)
