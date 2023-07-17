import Mathlib.Init.Set

variable (α:Type)(A B C: Set α)

example : A \ B = A ∩ B.compl := by
  refine Set.ext (λx:α => Iff.intro ?_ ?_)
  · intro (_ : x ∈ A \ B)
    assumption
  · intro (_ : x ∈ A ∩ Set.compl B)
    assumption
