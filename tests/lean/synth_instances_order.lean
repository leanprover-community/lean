/- See bug report and discussion at
https://leanprover-community.github.io/archive/113488general/35222rewritingandtypeclassinference.html#176608876
-/

class foo (G : Type)

class bar (G : Type) [foo G]

lemma silly {G : Type} [foo G] [bar G] : nonempty G ↔ nonempty G := iff.rfl

example (G : Type) [foo G] [bar G] (h : nonempty G) : nonempty G :=
begin
  rw silly,
  exact h
end

lemma silly2 {G : Type} [foo G] [bar G] : nonempty G → nonempty G := id

example (G : Type) [foo G] [bar G] (h : nonempty G) : nonempty G :=
begin
  apply silly2,
  exact h
end
