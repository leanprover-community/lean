prelude

import init.core

class inhabited (α : Type*) :=
(elem [] : α)

class is_unique (α : Type*) [inhabited α] : Prop :=
(eq_elem : ∀ (a : α), a = inhabited.elem α)

def is_unique.eq {α : Type*} ⟬is_unique α⟭ (a b : α) :
  a = b :=
(is_unique.eq_elem a).trans (is_unique.eq_elem b).symm
