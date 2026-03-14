import Mathlib.Computability.ContextFreeGrammar
import ContextFree.LeftmostDerivation
import LeanSearchClient

namespace ContextFreeRule

variable {r : ContextFreeRule T N}

def StrictRewrites (n : N) (u : List (Symbol T N)) := r = ⟨ n, u ⟩

lemma StrictRewrites.rewrites_leftmost (n : N) (u : List (Symbol T N))
  (h : r.StrictRewrites n u)
  : r.RewritesLeftmost [.nonterminal n] u := by
    grind only [eq_def, RewritesLeftmost.iff_exists_parts, RewritesLeftmost.input_output]

end ContextFreeRule

namespace ContextFreeGrammar

def StrictProduces (g : ContextFreeGrammar T) (n : g.NT) (u : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.StrictRewrites n u

lemma StrictProduces.produces_leftmost
  (g : ContextFreeGrammar T)
  (n : g.NT)
  (u : List (Symbol T g.NT))
  (h : g.StrictProduces n u) : g.ProducesLeftmost [.nonterminal n] u := by
    simp only [StrictProduces] at h
    obtain ⟨ r, ⟨ hr, h_rewrite ⟩ ⟩ := h
    use r; grind only [ContextFreeRule.StrictRewrites.rewrites_leftmost]

/-!
This definition is taken from the paper https://firsov.ee/cert-norm/cfg-norm.pdf
-/
mutual
  inductive Tree : (g : ContextFreeGrammar T) → g.NT → List T → Type u where
    | node
    {g : ContextFreeGrammar T}
    {n : g.NT}
    {s : List T}
    (children : List (Symbol T g.NT))
    (h_produces : g.StrictProduces n children)
    (forest : Forest g children s) : Tree g n s

  inductive Forest : (g : ContextFreeGrammar T) → List (Symbol T g.NT) → List T → Type u where
    | empty : Forest g [] []
    | terminal
    {g : ContextFreeGrammar T}
    {roots : List (Symbol T g.NT)}
    {s : List T}
    (t : T)
    (forest : Forest g roots s)
    : Forest g ((.terminal t) :: roots) (t :: s)
    | nonterminal
    {g : ContextFreeGrammar T}
    {roots : List (Symbol T g.NT)}
    {s₁ s₂ : List T}
    (n : g.NT)
    (tree : Tree g n s₁)
    (forest : Forest g roots s₂) : Forest g ((.nonterminal n) :: roots) (s₁ ++ s₂)
end

variable {g : ContextFreeGrammar T} {n : g.NT} {s : List T} {roots : List (Symbol T g.NT)}

def Tree.children (tree : Tree g n s) : List (Symbol T g.NT) :=
  match tree with
  | .node children _ _ => children

lemma Tree.strict_produces_children
  (tree : Tree g n s) : g.StrictProduces n (tree.children) := by
    grind [= StrictProduces.eq_def, = children.eq_def]

def TreeForest.induction.{u} :=
  fun {T : Type u} {g : ContextFreeGrammar T} {motive1 motive2} (node empty terminal nonterminal) =>
    And.intro
    (fun {n : g.NT} {s : List T} (t : g.Tree n s) =>
      @Tree.rec T g motive1 motive2 node empty terminal nonterminal n s t)
    (fun {roots : List (Symbol T g.NT)} {s : List T} (t : g.Forest roots s) =>
      @Forest.rec T g motive1 motive2 node empty terminal nonterminal roots s t)

/- def TreeForest.rec := -/
/-   fun {T} {g : ContextFreeGrammar T} {motive1 motive2} (node empty terminal nonterminal) => -/
/-     Prod.mk -/
/-     (fun {n : g.NT} {s : List T} (t : g.Tree n s) => -/
/-       @Tree.rec T g motive1 motive2 node empty terminal nonterminal n s t) -/
/-     (fun {roots : List (Symbol T g.NT)} {s : List T} (t : g.Forest roots s) => -/
/-       @Forest.rec T g motive1 motive2 node empty terminal nonterminal roots s t) -/

private lemma tree_forest_derives_leftmost_leaves :
  (∀ n : g.NT, ∀ s : List T, ∀ _ : Tree g n s,
  g.DerivesLeftmost [.nonterminal n] <| s.map Symbol.terminal)
  ∧
  (∀ roots : List (Symbol T g.NT), ∀ s : List T, ∀ _ : Forest g roots s,
  g.DerivesLeftmost roots <| s.map Symbol.terminal)
   := by
    apply TreeForest.induction
    · intro n s children h_produces forest h_derives
      apply StrictProduces.produces_leftmost at h_produces
      exact Relation.ReflTransGen.head h_produces h_derives
    · rfl
    · intro roots s t forest h_derives
      grind only [= List.map_cons, DerivesLeftmost.cons]
    · intro roots s₁ s₂ n tree forest h_n h_roots
      simp only [List.map_append]
      rw [← @List.singleton_append]
      apply DerivesLeftmost.append_left_of_derives_terminal
      · exact h_roots
      · exact h_n 

theorem Forest.derives_leftmost_leaves
  (forest : Forest g roots s)
  : g.DerivesLeftmost roots <| s.map Symbol.terminal := by
    apply tree_forest_derives_leftmost_leaves.right roots s forest

theorem Tree.derives_leftmost_leaves
  (tree : Tree g n s)
  : g.DerivesLeftmost [.nonterminal n] <| s.map Symbol.terminal := by
    apply tree_forest_derives_leftmost_leaves.left n s tree

/- private lemma tree_forest_of_derives -/
/-   : (∀ n : g.NT, ∀ s : List T, ∀ _ : Tree g n s, -/
/-     g.DerivesLeftmost [.nonterminal n] <| s.map Symbol.terminal) -/
/-     ∧ -/
/-     (∀ roots : List (Symbol T g.NT), ∀ s : List T, ∀ _ : Forest g roots s, -/
/-     g.DerivesLeftmost roots <| s.map Symbol.terminal) -/

def Forest.mkTerminals (ts : List T) : Forest g (ts.map Symbol.terminal) ts :=
  match ts with
  | [] =>
    Forest.empty
  | t :: ts =>
    by
      let forest := mkTerminals ts
      apply Forest.terminal t forest

mutual
noncomputable def Forest.of_derives
  {T : Type u_1} {g : ContextFreeGrammar T} {s : List T}
  {roots : List (Symbol T g.NT)}
  (h_derives : g.Derives roots <| s.map Symbol.terminal) : Forest g roots s :=
  have h_cases := h_derives.cases_head
  match Classical.dec (roots = List.map Symbol.terminal s) with
  | .isTrue h_terminal =>
    by
      rw [h_terminal]
      apply Forest.mkTerminals s
  | .isFalse h_not_terminal =>
    by
      have h_trans :
      ∃ c, g.Produces roots c ∧ g.Derives c (List.map Symbol.terminal s) := by grind
      let c := h_trans.choose
      have hc_eq : c = h_trans.choose := by rfl
      have hc := by apply h_trans.choose_spec
      rw [←hc_eq] at hc
      clear hc_eq
      obtain ⟨ h_produces, h_derives' ⟩ := hc
      let forest := Forest.of_derives h_derives'
      sorry
termination_by h_derives

noncomputable def Tree.of_derives
  {T : Type u_1} {g : ContextFreeGrammar T} {n : g.NT} {s : List T}
  (h_derives : g.Derives [.nonterminal n] <| s.map Symbol.terminal)
  : Tree g n s :=
  have h_cases :
  ∃ c, g.Produces [Symbol.nonterminal n] c
  ∧ g.Derives c (List.map Symbol.terminal s) := by
    have h := h_derives.cases_head
    rcases h with h | h
    · cases s with grind
    · exact h
  have children := h_cases.choose
  Tree.node children (by sorry) (sorry)
end

end ContextFreeGrammar
