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

-- Make sure other ways to comment out blocks still work:

example (p : Prop) : p ↔ p :=
begin
  split,
  sorry; { intro h, assumption, },
  { intro h, assumption, },
end

example (p : Prop) : p ↔ p :=
begin
  split,
  sorry <|> { intro h, assumption, },
  { intro h, assumption, },
end
