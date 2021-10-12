/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.core
/-!
# Boolean operations
-/

/-- `cond b x y` is `x` if `b = tt` and `y` otherwise. -/
@[inline] def {u} cond {a : Type u} : bool → a → a → a
| tt x y := x
| ff x y := y

/-- Boolean OR -/
@[inline] def bor : bool → bool → bool
| tt b := tt
| ff b := b

/-- Boolean AND -/
@[inline] def band : bool → bool → bool
| tt b := b
| ff b := ff

/-- Boolean NOT -/
@[inline] def bnot : bool → bool
| tt := ff
| ff := tt

/-- Boolean XOR -/
@[inline] def bxor : bool → bool → bool
| tt ff  := tt
| ff tt  := tt
| _  _   := ff

infixl ` || `:65 := bor
infixl ` && `:70 := band
