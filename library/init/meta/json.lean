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

protected meta constant parse : string → option json
protected meta constant unparse : json → string

meta def to_format : json → format
| (of_string s) := string.quote s
| (of_int i) := to_string i
| (of_float f) := to_string f
| (of_bool tt) := "true"
| (of_bool ff) := "false"
| (null) := "null"
| (object kvs) := "{ " ++ (format.group $ format.nest 2 $ format.join $ list.intersperse (", " ++ format.line) $ kvs.map $ λ ⟨k,v⟩, string.quote k ++ ":" ++ to_format v) ++ "}"
| (array js) := list.to_format $ js.map to_format

meta instance : has_to_format json := ⟨to_format⟩
meta instance : has_to_string json := ⟨json.unparse⟩
meta instance : has_repr json := ⟨json.unparse⟩

end json