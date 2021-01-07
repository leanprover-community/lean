open widget

variables {α:Type}

meta def Hello : component string α := component.pure (λ s, ["hello, ", s, ", good day!"])

#html (Hello "lean") -- renders "hello, lean, good day!"