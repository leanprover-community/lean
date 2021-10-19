
namespace A

def x := 1

def _root_.B.x := 1

end A

def C.x := 1

run_cmd tactic.add_aux_decl `D.x `(ℕ) `(1) ff

open A B C D
