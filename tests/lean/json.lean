#eval to_string $ json.parse $ "[0.7]"
#eval to_string $ json.parse "{}"
#eval to_string $ json.unparse (json.object [])
run_cmd tactic.success_if_fail $ json.parse "spurgles"

meta def ball : list bool → bool :=
λ xs, xs.foldl band tt

meta instance : decidable_eq native.float := by apply_instance

meta def json.compare : Π (x y : json), bool
| (json.of_string s) (json.of_string s') := s = s'
| (json.of_int k) (json.of_int k') := k = k'
| (json.of_float x) (json.of_float x') := x = x'
| (json.of_bool b) (json.of_bool b') := b = b'
| (json.null) (json.null) := tt
| (json.object kvs) (json.object kvs') := (list.zip kvs kvs').foldr
  (λ ⟨⟨k₁, v₁⟩, ⟨k₂, v₂⟩⟩ acc,
  json.compare k₁ k₂ && json.compare v₁ v₂ && acc) tt
| (json.array args) (json.array args') := (list.zip args args').foldr
  (λ ⟨j₁, j₂⟩ acc, acc && json.compare j₁ j₂) tt
| _ _ := ff

meta def test_parse_unparse : tactic unit := do {
  f ← native.float.of_string "0.4",
  let obj : json := json.object
    [
        ("hello", f)
      , ("world", json.array
          [
              json.null
            , tt
            , ff
            , json.of_int (-1)
            , json.of_int 1
            , json.of_int (-1000)
            , json.of_int 3
            , "this is a \"string with an annoying quote in it"
          ]
        )
    ],
  let obj_msg := json.unparse obj,
  obj' ← json.parse obj_msg,
  guard (obj.compare obj') <|> tactic.trace format!"FAILED:\n{obj}\n{obj'}",

  let obj_msg' := json.unparse obj',
  guard (obj_msg = obj_msg') <|> tactic.trace format!"FAILED:\n{obj_msg}\n{obj_msg'}"
}

#eval test_parse_unparse

-- negative numbers should unparse to signed numbers
run_cmd do
  j@(json.of_int i) ← json.parse "-1",
  tactic.trace (to_string i),-- buggy version gave 4294967295
  tactic.trace j.to_format,
  tactic.trace j.unparse
