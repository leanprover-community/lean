/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat.basic
namespace nat

protected def div_core (y : ℕ) : ℕ → ℕ → ℕ
| 0 _ := 0
| (fuel+1) x := if h : 0 < y ∧ y ≤ x then div_core fuel (x - y) + 1 else 0

protected def div (x y : ℕ) : ℕ :=
nat.div_core y x x

instance : has_div nat :=
⟨nat.div⟩

protected def mod_core (y : ℕ) : ℕ → ℕ → ℕ
| 0 x := x
| (fuel+1) x := if h : 0 < y ∧ y ≤ x then mod_core fuel (x - y) else x

protected def mod (x y : ℕ) : ℕ :=
nat.mod_core y x x

instance : has_mod nat :=
⟨nat.mod⟩

end nat
