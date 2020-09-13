-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.core

@[inline] def {u} cond {a : Type u} : bool → a → a → a
| tt x y := x
| ff x y := y

@[inline] def bor : bool → bool → bool
| tt b := tt
| ff b := b

@[inline] def band : bool → bool → bool
| tt b := b
| ff b := ff

@[inline] def bnot : bool → bool
| tt := ff
| ff := tt

@[inline] def bxor : bool → bool → bool
| tt ff  := tt
| ff tt  := tt
| _  _   := ff

notation x || y := bor x y
notation x && y := band x y
