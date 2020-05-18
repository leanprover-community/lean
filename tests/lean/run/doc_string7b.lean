import .doc_string7a
open tactic

#eval do
ds ← olean_doc_strings,
let ds := (do
    ⟨some fn, d⟩ ← ds | [],
    guard $ fn.backn 17 = "doc_string7a.lean",
    d),
trace ds,
guard $ ds = [(⟨1, 0⟩, "a"), (⟨2,0⟩, "b")]