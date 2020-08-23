/-
Copyright (c) E.W.Ayers 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import init.data
import init.meta.float

meta inductive json : Type
| of_string : string → json
| of_int : int → json
| of_float : native.float → json
| of_bool : bool → json
| null : json
| object : list (string × json) → json
| array : list json → json

namespace json

meta instance string_coe : has_coe string json := ⟨json.of_string⟩
meta instance int_coe : has_coe int json := ⟨json.of_int⟩
meta instance float_coe : has_coe native.float json := ⟨json.of_float⟩
meta instance bool_coe : has_coe bool json := ⟨json.of_bool⟩
meta instance array_coe : has_coe (list json) json := ⟨json.array⟩
meta instance : inhabited json := ⟨json.null⟩

end json