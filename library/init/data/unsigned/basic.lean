/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.fin.basic

open nat
def unsigned_sz : nat := succ 4294967295

def unsigned := fin unsigned_sz

namespace unsigned
/- We cannot use tactic dec_trivial here because the tactic framework has not been defined yet. -/
private lemma zero_lt_unsigned_sz : 0 < unsigned_sz :=
zero_lt_succ _

/- Later, we define of_nat using mod, the following version is used to define the metaprogramming system. -/
protected def of_nat' (n : nat) : unsigned :=
if h : n < unsigned_sz then ⟨n, h⟩ else ⟨0, zero_lt_unsigned_sz⟩

instance : has_zero unsigned := ⟨⟨0, succ_pos _⟩⟩
instance : has_one unsigned  := ⟨⟨1, succ_le_succ (succ_pos _)⟩⟩

def to_nat (c : unsigned) : nat := c.val

end unsigned

instance : decidable_eq unsigned :=
have decidable_eq (fin unsigned_sz), from fin.decidable_eq _,
this
