section
universes v u

class category (C : Type u) := (hom : C → C → Type v)
end

section
universes v u

variables (C : Type u) [category.{v} C]

def End (X : C) := category.hom X X

end
