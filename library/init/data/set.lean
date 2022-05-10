/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive
import init.control.lawful

universes u v
def set (α : Type u) := α → Prop

def set_of {α : Type u} (p : α → Prop) : set α := p
