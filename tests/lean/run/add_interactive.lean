namespace foo
namespace bla
open lean.parser interactive interactive.types

/-- test doc string -/
meta def my_exact (q : parse texpr) :=
tactic.interactive.exact q

/- Copy tactic my_exact to tactic.interactive. -/
run_cmd add_interactive [`my_exact]
end bla

example : true :=
begin
  my_exact trivial
end

open tactic

run_cmd do
  old_doc ← doc_string `foo.bla.my_exact,
  new_doc ← doc_string `tactic.interactive.my_exact,
  if old_doc = new_doc then skip else fail "doc strings do not match"

end foo
