def successors : set nat := {(x + 1) | x : nat}
lemma successors_correct : successors = {x | ∃ y, y + 1 = x} := rfl

variables {x' : nat}

def successors' : set nat := {(x' + 1) | x'}
lemma successors_correct' : successors = successors' := rfl

def x'' := 0

def successors'' : set nat := {(x'' + 1) | x''}
lemma successors_correct'' : successors = successors'' := rfl

def f : nat -> nat := λ x, x + 1

def successors''' : set nat := {(f x) | x}
lemma successors_correct''' : successors = successors''' := rfl

def between_1_and_5 : set nat := {(x + 1) | x < 5}
lemma between_1_and_5_correct :
  between_1_and_5 = {y | ∃ (x : nat) (h : x < 5), x + 1 = y} := rfl

def triangle : set (nat × nat) := {(x, y) | (x y) (h : x + y < 5)}
lemma triangle_correct :
  triangle = {xy | ∃ (x y : nat) (h : x + y < 5), (x, y) = xy} := rfl

