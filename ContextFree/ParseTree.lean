import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Nat.Init
import ContextFree.LeftmostDerivation
import ContextFree.Basic
import LeanSearchClient

namespace ContextFreeGrammar

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

mutual
  def Tree.sizeOf
  {g : ContextFreeGrammar T}
  {n : g.NT}
  {s : List T}
  (tree : Tree g n s) : Nat :=
    match tree with
    | .node _ _ forest => 1 + forest.sizeOf

  def Forest.sizeOf
  {g : ContextFreeGrammar T}
  {roots : List (Symbol T g.NT)}
  {s : List T}
  (forest : Forest g roots s) : Nat :=
    match forest with
    | .empty => 0
    | .terminal _ forest' =>
      1 + forest'.sizeOf
    | .nonterminal _ tree forest' =>
      1 + tree.sizeOf + forest'.sizeOf
end

def Forest.append
  {g : ContextFreeGrammar T}
  {roots₁ : List (Symbol T g.NT)}
  {roots₂ : List (Symbol T g.NT)}
  {s₁ s₂ : List T}
  (f₁ : Forest g roots₁ s₁)
  (f₂ : Forest g roots₂ s₂) : Forest g (roots₁ ++ roots₂) (s₁ ++ s₂) := by
    cases f₁
    case empty =>
      exact f₂
    case terminal roots s₁' t forest =>
      let f := Forest.append forest f₂
      apply Forest.terminal
      exact f
    case nonterminal roots xs ys n tree forest  =>
      let f := Forest.append forest f₂
      rw [List.append_assoc]
      apply Forest.nonterminal
      · exact tree
      · exact f

def Tree.toForest
  {g : ContextFreeGrammar T}
  {n : g.NT}
  {s : List T}
  (tree : Tree g n s) : Forest g [.nonterminal n] s := by
    rw [←List.append_nil s]
    apply Forest.nonterminal
    · exact tree
    · exact Forest.empty

variable {g : ContextFreeGrammar T} {n : g.NT} {s : List T} {roots : List (Symbol T g.NT)}

instance Tree.instSizeOf : SizeOf (Tree g n s) where
  sizeOf := sizeOf

instance Forest.instSizeOf : SizeOf (Forest g roots s) where
  sizeOf := sizeOf

lemma Tree.sizeOf_node_forest_lt_self
  (children : List (Symbol T g.NT))
  (h_produces : g.StrictProduces n children)
  (forest : Forest g children s)
  : SizeOf.sizeOf forest < SizeOf.sizeOf (Tree.node children h_produces forest) := by
    reduce; grind

lemma Forest.sizeOf_terminal_forest_lt_self
  (t : T)
  (forest : Forest g roots s)
  : SizeOf.sizeOf forest < SizeOf.sizeOf (Forest.terminal t forest) := by
    reduce; grind

lemma Forest.sizeOf_nonterminal_tree_lt_self
  (n : g.NT)
  (tree : Tree g n s₁)
  (forest : Forest g roots s₂)
  : SizeOf.sizeOf tree < SizeOf.sizeOf (Forest.nonterminal n tree forest) := by
    reduce; grind

lemma Forest.sizeOf_nonterminal_forest_lt_self
  (n : g.NT)
  (tree : Tree g n s₁)
  (forest : Forest g roots s₂)
  : SizeOf.sizeOf forest < SizeOf.sizeOf (Forest.nonterminal n tree forest) := by
    reduce; grind

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

private lemma tree_forest_derives_leftmost_yield :
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

theorem Forest.derives_leftmost_yield
  (forest : Forest g roots s)
  : g.DerivesLeftmost roots <| s.map Symbol.terminal := by
    apply tree_forest_derives_leftmost_yield.right roots s forest

theorem Tree.derives_leftmost_yield
  (tree : Tree g n s)
  : g.DerivesLeftmost [.nonterminal n] <| s.map Symbol.terminal := by
    apply tree_forest_derives_leftmost_yield.left n s tree

def Forest.ofString
  (s : List T) : Forest g (s.map Symbol.terminal) s :=
  match s with
  | [] => Forest.empty
  | t :: ts =>
    Forest.terminal t (Forest.ofString ts)

theorem Tree.of_derivation
  {g : ContextFreeGrammar T} {n : g.NT} {s : List T}
  (h_derives : g.Derives [.nonterminal n] <| s.map Symbol.terminal)
  : ∃ t : Tree g n s, True := by
    generalize hn : [Symbol.nonterminal n] = ns at *
    generalize hs : List.map Symbol.terminal s = s' at *
    induction h_derives using Relation.ReflTransGen.head_induction_on with
    | refl =>
      sorry
    | head =>
      sorry

-- I tried proving this a lot bot unfortunately proof irrelevance makes doing strong induction really hard and I'll have to reinvent Derives with Type instead of Prop to make this work which is a chore
#check Relation.ReflTransGen.rec
theorem Forest.of_derivation
  {g : ContextFreeGrammar T} {roots : List (Symbol T g.NT)} {s : List T}
  (h_derives : g.Derives roots <| s.map Symbol.terminal)
  : ∃ f : Forest g roots s, True := by
    sorry
    /- generalize hs : List.map Symbol.terminal s = s' at * -/
    /- rcases h_derives.cases_head -/
    /- case inl => -/
    /-   subst_eqs -/
    /-   use Forest.ofString s -/
    /- case inr h => -/
    /-   obtain ⟨ u, h_u, h_us ⟩ := h -/
    /-   subst_eqs -/
    /-   change g.Derives u (List.map Symbol.terminal s) at h_us -/
    /-   apply Produces.exists_parts at h_u -/
    /-   obtain ⟨ r, hr, p, q, hroots, hu ⟩ := h_u; subst_eqs -/
    /-   apply Derives.of_app_derives at h_us -/
    /-   obtain ⟨ xs, ys, hxs, hys, hs ⟩ := h_us; subst_eqs -/
    /-   apply Derives.of_app_derives at hxs -/
    /-   obtain ⟨ zs, ws, hzs, hws, hxs ⟩ := hxs; subst_eqs -/
    /-   have fp := Forest.of_derivation hys -/
    /-   sorry -/
    /--/
end ContextFreeGrammar
