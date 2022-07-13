#eval to_string $ json.parse $ "[0.7]"
#eval to_string $ json.parse "{}"
#eval to_string $ json.unparse (json.object [])
run_cmd tactic.success_if_fail $ json.parse "spurgles"

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

run_cmd do
  -- this is the maximum value of a float32
  let obj_i : json := json.of_int 0xFFFFFF00000000000000000000000000,
  let msg := json.unparse obj_i,
  obj_f ← json.parse msg,
  -- the large int is turned into a float
  guard (obj_f = json.of_float (0xFFFFFF00000000000000000000000000 : native.float))

run_cmd do
  -- this is the maximum integer that after truncation fits a float32
  let obj_i : json := json.of_int 0xFFFFFF7FFFFFFFFFFFFFFFFFFFFFFFFF,
  let msg := json.unparse obj_i,
  obj_f ← json.parse msg,
  -- the large int is truncated
  guard (obj_f = json.of_float (0xFFFFFF00000000000000000000000000 : native.float))

run_cmd do
  -- this is the smallest integer that does not fit in a float32
  let obj_i : json := json.of_int 0xFFFFFF80000000000000000000000000,
  let msg := json.unparse obj_i,
  obj_f ← json.parse msg,
  -- the large int overflows to infinity, which cannot be stored in json
  guard (obj_f = json.null)

run_cmd do
  -- this is the smallest integer that does not fit in a float32
  let msg : string := to_string 0xFFFFFF80000000000000000000000000,
  obj_f ← json.parse msg,
  -- the large int overflows to (https://github.com/nlohmann/json does not support big integers)
  guard (obj_f = json.of_float native.float.infinity)
