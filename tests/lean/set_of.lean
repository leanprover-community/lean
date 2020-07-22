#check {x : nat | x > 0}
#check {x | x > 0}
#check {p : nat × nat | p.1 > p.2 }

set_option pp.binder_types false

#check {x : nat | x > 0}
#check {x | x > 0}
#check {p : nat × nat | p.1 > p.2 }

def successors : set nat := {(x + 1) | x}
lemma successors_correct : successors = {x | ∃ y, y + 1 = x} := rfl

variables {x' : nat}

def successors' : set nat := {(x' + 1) | x'}
lemma successors_correct' : successors = successors' := rfl

def x'' := 0

def successors'' : set nat := {(x'' + 1) | x''}
lemma successors_correct'' : successors = successors'' := rfl
