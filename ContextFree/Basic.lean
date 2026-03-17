import Mathlib.Tactic.Lemma

abbrev List.map_mem
  (xs : List α)
  (f : (a : α) → a ∈ xs → β) : List β := xs.pmap f (by grind)

lemma List.mem_map_mem_iff
  (xs : List α)
  (f : (a : α) → a ∈ xs → β)
  (y : β) : y ∈ xs.map_mem f ↔ ∃ x, ∃ _ : x ∈ xs, y = f x (by grind) := by grind

