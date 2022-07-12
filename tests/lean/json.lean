#eval to_string $ json.parse $ "[0.7]"
#eval to_string $ json.parse "{}"
#eval to_string $ json.unparse (json.object [])
run_cmd tactic.success_if_fail $ json.parse "spurgles"

meta def ball : list bool → bool :=
λ xs, xs.foldl band tt

meta instance : decidable_eq native.float := by apply_instance

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
            , json.of_int 1
            , json.of_int 2
            , json.of_int 3
            , json.of_int (-1)
            , json.of_int (-1000)
            -- minimum int64_t and maximum uint64_t. Larger integers overflow to floats
            , json.of_int (-0x8000000000000000)
            , json.of_int (0xFFFFFFFFFFFFFFFF)
            , "this is a \"string with an annoying quote in it"
          ]
        )
    ],
  let obj_msg := json.unparse obj,
  obj' ← json.parse obj_msg,
  guard (obj = obj') <|> tactic.trace format!"FAILED:\n{obj}\n{obj'}",

  let obj_msg' := json.unparse obj',
  guard (obj_msg = obj_msg') <|> tactic.trace format!"FAILED:\n{obj_msg}\n{obj_msg'}"
}

#eval test_parse_unparse
