example {a b c : ℕ} : (a * b) * c = (a * b) * c := begin
  conv {
    for (_ * _) [1] {
      rw does_not_exist,
    },
  },
end
