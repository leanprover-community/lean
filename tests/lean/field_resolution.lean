section structures

structure foo :=
(a : ℕ)

structure bar extends foo :=
(b : ℕ)

def foo.s : foo := {a := 37}
def bar.s : bar := {a := 17, b := 22}

-- (error) prefer "unknown identifier"
#check foo.c

-- true fields
#eval foo.s.a
#eval bar.s.a
#eval bar.s.b

-- anonymous field notation
#eval foo.s.1
#eval bar.s.1.1
#eval bar.s.2

def foo.inc_a (s : foo) : ℕ := s.a + 1
def bar.inc_b (s : bar) : ℕ := s.b + 1

-- extended dot notation (method resolution)
#eval foo.s.inc_a
#eval bar.s.inc_a
#eval bar.s.inc_b

def foo.add_a (n : ℕ) (s : foo) : ℕ := s.a + n

example : foo.s.add_a 1 = foo.s.inc_a := rfl
example : bar.s.add_a 1 = bar.s.inc_a := rfl

-- (error) insufficient arguments is error (yet could be lambda like in Lean 4)
#check foo.s.add_a
--example : foo.s.add_a = λ n, foo.s.add_a n := rfl
#check bar.s.add_a
--example : bar.s.add_a = λ n, bar.s.add_a n := rfl

def foo.add_b_of_eq (n : ℕ) {m : ℕ} (h : n = m) (s : foo) : ℕ := s.a + m

-- (error) insufficient arguments (trickier example for synthesizing lambda)
#check foo.s.add_b_of_eq

def foo.blah (n : ℕ) : ℕ := n

-- (error) invalid field notation, no explicit argument of type (foo ...)
#check foo.s.blah 37
#check bar.s.blah 37

end structures

section local_constants

-- Without arguments
def list.double {α : Type*} : list α → list α
| [] := []
| (x :: xs) := x :: x :: xs.double

-- With arguments
def list.map' {α β : Type*} : (α → β) → list α → list β
| _ [] := []
| f (x :: xs) := f x :: xs.map' f

end local_constants

section classes

class baz (α : Type*) :=
(a : α)
(b : ℕ → α)

-- projection for class instance
example (α : Type*) (I : baz α) : I.a = I.a := rfl
-- projection for class instance with arguments
example (α : Type*) (I : baz α) : I.b 37 = I.b 37 := rfl
-- plain fully qualified name
example (α : Type*) [baz α] : (baz.b 37 : α) = baz.b 37 := rfl

end classes

section functions

lemma function.mt {p q : Prop} (h : p → q) : ¬ q → ¬ p := mt h

example {p q : Prop} (hnp : ¬ p) (h : q → p) : ¬ q := h.mt hnp

def function.apply {α β : Type*} (x : α) (f : α → β) : β := f x

example : (+ 3).apply 1 = 4 := rfl
-- (error) insufficient number of arguments is error (yet could be a lambda like in Lean 4)
#check λ (x : ℕ), (+ x).apply
--example : (λ (x : ℕ), (+ x).apply) = (λ x y, y + x) := rfl
--example : (λ (x : ℕ), (+ x).apply) = (λ (y : ℕ), (+ y).apply) := rfl

end functions

section aliases

def Set (α : Type) := α → Prop
def Set.union {α : Type} (s₁ s₂ : Set α) : Set α := λ a, s₁ a ∨ s₂ a
def FinSet (n : ℕ) := fin n → Prop

export Set (renaming union → FinSet.union)

example (x y : FinSet 10) : FinSet 10 :=
  x.union y -- Works

end aliases
