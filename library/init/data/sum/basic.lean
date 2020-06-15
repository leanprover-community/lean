/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
prelude
import init.logic

notation α ⊕ β := sum α β

universes u v

namespace sum

variables {α : Type u} {β : Type v}

instance inhabited_left [h : inhabited α] : inhabited (α ⊕ β) :=
⟨inl (default α)⟩

instance inhabited_right [h : inhabited β] : inhabited (α ⊕ β) :=
⟨inr (default β)⟩

def get_left : α ⊕ β → option α
| (inl a) := some a
| _ := none

def get_right : α ⊕ β → option β
| (inr b) := some b
| _ := none

def is_left : α ⊕ β → bool
| (inl _) := tt
| (inr _) := ff

def is_right : α ⊕ β → bool
| (inl _) := ff
| (inr _) := tt

end sum
