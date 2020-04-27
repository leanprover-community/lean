/--
/- /- /- nested docstring -/ -/ -/
-/
def foo : string := "/- /- /- nested docstring -/ -/ -/"
open tactic
run_cmd do
  doc ← doc_string `foo,
  if doc = foo then skip
  else fail ("doc string of `foo` was:\n" ++ doc ++
             "\n\nexpected:\n" ++ foo)
