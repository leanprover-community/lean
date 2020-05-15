@[simp] lemma subsingleton.eq {α} [subsingleton α] (a b : α) : a = b ↔ true := by cc

example {α} [subsingleton α] (a b : α) : a = b := by simp -- works


-- let's generalize this to unique
class unique (α : Sort*) extends inhabited α := [ss : subsingleton α]
attribute [instance] unique.ss

@[simp] lemma unique.eq {α} [unique α] (a b : α) : a = b ↔ true :=
subsingleton.eq _ _


example {α} [subsingleton α] (a b : α) : a = b := by simp -- still works!!!