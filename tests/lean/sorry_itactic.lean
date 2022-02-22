example (p : Prop) : p ↔ p :=
begin
  split,
  sorry { intro h, assumption, },
  { intro h, assumption, },
end

example (p : Prop) : p ↔ p :=
begin
  split,
  sorry,
  { intro h, assumption, },
end
