universes u

-- make all subsingleton instances time out
@[instance] axiom loop {α} [subsingleton (unit → α)] : subsingleton α

-- simp should not synthesize subsingleton instances
lemma zou (α : Type u) (x y : α) (h : x = y) : x = y :=
by simp only [h]
