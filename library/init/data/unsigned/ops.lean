/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.unsigned.basic init.data.nat

namespace unsigned

def of_nat (n : nat) : unsigned :=
⟨n % nat.succ _, nat.mod_lt _ (nat.zero_lt_succ _)⟩

private lemma mlt {n b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.mod_lt _ h
| (a+1) h :=
  have n > 0, from lt_trans (nat.zero_lt_succ _) h,
  nat.mod_lt _ this

protected def add : unsigned → unsigned → unsigned
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a + b) % _, mlt h⟩

instance : has_add unsigned := ⟨unsigned.add⟩

end unsigned
