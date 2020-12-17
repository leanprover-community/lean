/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic

lemma punit_eq (a b : punit) : a = b :=
punit.rec_on a (punit.rec_on b rfl)

lemma punit_eq_star (a : punit) : a = punit.star :=
punit_eq a punit.star

instance : subsingleton punit :=
subsingleton.intro punit_eq

instance : inhabited punit :=
⟨punit.star⟩

instance : decidable_eq punit :=
λ a b, is_true (punit_eq a b)
