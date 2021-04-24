example (p : Prop) (h1 : p) : p :=
begin
  assumption?,
end

example (p : Prop) (h2 : ∀ {x : ℕ}, p) : ∀ x : ℕ, p :=
begin
  assumption?,
end
