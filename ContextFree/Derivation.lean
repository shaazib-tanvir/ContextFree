import Mathlib.Computability.ContextFreeGrammar
import ContextFree.Basic

namespace ContextFreeGrammar

inductive Derives' (g : ContextFreeGrammar T)
: List (Symbol T g.NT) → List (Symbol T g.NT) → Type _ where
  | refl (u : List (Symbol T g.NT)) : g.Derives' u u
  | trans
  {u v w : List (Symbol T g.NT)}
  (h_produces : g.Produces u v)
  (derives : g.Derives' v w)
  : g.Derives' u w

variable {g : ContextFreeGrammar T}

def Derives'.sizeOf
  (derives : Derives' g u v) : Nat :=
  match derives with
  | refl u =>
    u.length
  | trans _ child_derives =>
    1 + child_derives.sizeOf

@[simp, grind =]
lemma Derives'.sizeOf_refl_eq_length
  (u : List (Symbol T g.NT))
  : (Derives'.refl u).sizeOf = u.length := by
    simp [Derives'.sizeOf]

@[simp, grind =]
lemma Derives'.sizeOf_trans
  {u v w : List (Symbol T g.NT)}
  (h_produces : g.Produces u v)
  (derives : g.Derives' v w)
  : (Derives'.trans h_produces derives).sizeOf = 1 + derives.sizeOf := by rfl

lemma Derives'.sizeOf_child_lt_parent
  {u v w : List (Symbol T g.NT)}
  (h_produces : g.Produces u v)
  (derives : g.Derives' v w)
  : derives.sizeOf < (Derives'.trans h_produces derives).sizeOf := by
    simp [Derives'.sizeOf]

instance Derives'.instSizeOf : SizeOf (Derives' g u v) where
  sizeOf := sizeOf

@[simp, grind =]
lemma Derives'.sizeOf_def (derives : g.Derives' u v)
  : SizeOf.sizeOf derives = derives.sizeOf := by rfl

lemma Derives.of_derives'
  {u v : List (Symbol T g.NT)}
  (derives' : g.Derives' u v) : g.Derives u v := by
  induction derives'
  case refl => grind
  case trans => grind only [Produces.trans_derives]

lemma Derives'.of_derives
  {u v : List (Symbol T g.NT)}
  (h_derives : g.Derives u v) : ∃ _ : g.Derives' u v, True := by
    induction h_derives using Relation.ReflTransGen.head_induction_on with
    | refl =>
      use Derives'.refl v
    | head h_produces h_derives h_derives' =>
      obtain ⟨ derives', - ⟩ := h_derives'
      use (by
      apply Derives'.trans
      · apply h_produces
      · apply derives')

noncomputable def Derives'.ofDerives
  {u v : List (Symbol T g.NT)}
  (h_derives : g.Derives u v) : g.Derives' u v := Derives'.of_derives h_derives |>.choose

lemma Derives'.of_append_derives'
  {xs ys : List (Symbol T g.NT)}
  {s : List T}
  (derives' : g.Derives' (xs ++ ys) (List.map Symbol.terminal s))
  :
  ∃ zs ws : List T,
  (∃ derives₁ : (g.Derives' xs (List.map Symbol.terminal zs)),
    SizeOf.sizeOf derives₁ ≤ SizeOf.sizeOf derives') ∧
  (∃ derives₂ : (g.Derives' ys (List.map Symbol.terminal ws)),
    SizeOf.sizeOf derives₂ ≤ SizeOf.sizeOf derives') ∧
  (s = zs ++ ws) := by
    generalize hu : xs ++ ys = u at *
    generalize hs' : List.map Symbol.terminal s = s' at *
    induction derives' generalizing xs ys s with
    | refl =>
      subst_eqs; symm at hs'
      apply list_symbol_split at hs'
      obtain ⟨ zs, ws, hxs, hys, hs ⟩ := hs'
      use zs; use ws; subst_eqs
      constructor
      · use Derives'.refl <| zs.map Symbol.terminal
        simp
      · constructor
        · use Derives'.refl <| ws.map Symbol.terminal
          simp
        · rfl
    | @trans v w x hvw hwx hi =>
      subst_eqs
      apply Produces.exists_parts at hvw
      obtain ⟨ r, hr, p, q, h_xs_ys, hw ⟩ := hvw
      subst_eqs
      rw [List.append_eq_append_iff] at h_xs_ys
      obtain ⟨ as, hp, hq ⟩ | ⟨ bs, hp, hq ⟩ := h_xs_ys <;> subst_eqs
      · rw [List.append_eq_append_iff] at hp
        obtain ⟨ cs, hxs, hinput ⟩ | ⟨ ds, hp, has ⟩ := hp <;> subst_eqs
        · cases cs <;> simp_all only [List.append_assoc, Derives'.sizeOf_def, List.nil_append]
          · subst_eqs
            specialize @hi p (r.output ++ q) s (by rfl) (by rfl)
            obtain ⟨ zs, ws, ⟨ derives₁, h₁ ⟩, ⟨ derives₂, h₂ ⟩, hs ⟩ := hi; subst_eqs
            use zs; use ws
            constructor
            · use (by
                rw [List.append_nil]
                exact derives₁)
              simp [*]
              grind only
            · constructor
              · use (by
                  apply Derives'.trans
                  · change g.Produces ([.nonterminal r.input] ++ q) (r.output ++ q)
                    use r
                    constructor
                    · exact hr
                    · solve_by_elim
                  · exact derives₂)
                simp [*]
              · rfl
          case cons cs tail =>
            simp only [List.cons_append, List.cons.injEq, List.nil_eq,
              List.append_eq_nil_iff] at hinput
            obtain ⟨ hinput, htail, has ⟩ := hinput
            subst_eqs
            specialize @hi (p ++ r.output) q s (by simp) (by rfl)
            obtain ⟨ zs, ws, ⟨ derives₁, h₁ ⟩, ⟨ derives₂, h₂ ⟩, hs ⟩ := hi; subst_eqs
            use zs; use ws
            constructor
            · use (by
                apply Derives'.trans
                · change g.Produces (p ++ [.nonterminal r.input]) (p ++ r.output)
                  use r
                  constructor
                  · exact hr
                  · rw [←List.append_nil (p ++ [Symbol.nonterminal r.input]),
                    ←List.append_nil (p ++ r.output)]
                    grind only [ContextFreeRule.rewrites_of_exists_parts]
                · use derives₁)
              simp [*]
            · constructor
              · use derives₂
                grind only [= Derives'.sizeOf_trans]
              · rfl
        · specialize @hi xs (ds ++ r.output ++ q) s (by simp) (by rfl)
          obtain ⟨ zs, ws, ⟨ derives₁, h₁ ⟩, ⟨ derives₂, h₂ ⟩, hs ⟩ := hi; subst_eqs
          use zs; use ws
          constructor
          · use derives₁
            simp only [Derives'.sizeOf_def, Derives'.sizeOf_trans]; grind
          · constructor
            · use (by
                apply Derives'.trans
                · change g.Produces (ds ++ [.nonterminal r.input] ++ q) (ds ++ r.output ++ q)
                  use r; grind only [ContextFreeRule.rewrites_of_exists_parts]
                · exact derives₂)
              simp only [Derives'.sizeOf_def, Derives'.sizeOf_trans, Nat.add_le_add_iff_left]
              exact h₂
            · rfl
      · specialize @hi (p ++ r.output ++ bs) ys s (by simp) (by rfl)
        obtain ⟨ zs, ws, ⟨ derives₁, h₁ ⟩, ⟨ derives₂, h₂ ⟩, hs ⟩ := hi; subst_eqs
        use zs; use ws
        constructor
        · use (by
            apply Derives'.trans
            · change g.Produces (p ++ [.nonterminal r.input] ++ bs) (p ++ r.output ++ bs)
              use r; grind only [ContextFreeRule.rewrites_of_exists_parts]
            · exact derives₁)
          simp only [Derives'.sizeOf_def, Derives'.sizeOf_trans, Nat.add_le_add_iff_left]
          exact h₁
        · constructor
          · use derives₂
            simp only [Derives'.sizeOf_def, Derives'.sizeOf_trans]
            grind
          · rfl

end ContextFreeGrammar
