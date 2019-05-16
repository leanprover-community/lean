import system.io

def this_dir := "tests/lean"

meta def lean_root : tactic string :=
tactic.unsafe_run_io $ do
  dir ← io.env.get_cwd,
  return $ list.as_string $ dir.to_list.take (dir.length - this_dir.length - 1)

open tactic

meta def mk_def {α} [reflected α] [has_reflect α] (n : name) (tac : tactic α) : tactic unit :=
do let t := `(α),
   v ← tac,
   add_decl $ mk_definition n [] t (reflect v)

run_cmd mk_def `root_dir lean_root

meta def test' : tactic unit := (tactic.unsafe_run_io
(do io.env.set_cwd "lean",
    io.env.get_cwd >>= io.put_str_ln) >> failed)

run_cmd test' <|> trace "foo"

def strip_prefix (p s : string) : string :=
list.as_string $ s.to_list.drop p.length

meta def test : tactic unit := tactic.unsafe_run_io $
do io.env.get_cwd >>= io.put_str_ln ∘ strip_prefix root_dir,
   io.env.set_cwd "..",
   io.env.get_cwd >>= io.put_str_ln ∘ strip_prefix root_dir

run_cmd (test >> test >> tactic.failed) <|> test
