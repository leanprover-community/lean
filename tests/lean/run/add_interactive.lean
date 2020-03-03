namespace foo
namespace bla
open lean.parser interactive interactive.types

/-- test doc string -/
meta def my_exact (q : parse texpr) :=
tactic.interactive.exact q

/- Copy tactic my_exact to tactic.interactive. -/
run_cmd add_interactive [`my_exact]

/- Copy tactic my_exact to test_namespace. -/
run_cmd add_interactive [`my_exact] `test_namespace
end bla

example : true :=
begin
  my_exact trivial
end

open tactic

run_cmd do
  old_doc ← doc_string `foo.bla.my_exact,
  new_doc ← doc_string `tactic.interactive.my_exact,
  if old_doc = new_doc then skip else fail "doc strings of foo.bla.my_exact and tactic.interactive.my_exact do not match"

run_cmd do
  old_doc ← doc_string `foo.bla.my_exact,
  new_doc ← doc_string `test_namespace.my_exact,
  if old_doc = new_doc then skip else fail "doc strings of foo.bla.my_exact and test_namespace.my_exact do not match"

end foo
