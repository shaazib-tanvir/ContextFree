import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Nat.Init
import ContextFree.LeftmostDerivation
import ContextFree.Basic
import ContextFree.Derivation
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

def Tree.ofForest
  {g : ContextFreeGrammar T}
  {n : g.NT}
  {s : List T}
  (forest : Forest g [.nonterminal n] s) : Tree g n s := by
    rcases forest
    expose_names
    rcases forest
    rw [List.append_nil]
    exact tree

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

lemma Forest.of_derives'
  {g : ContextFreeGrammar T}
  {roots : List (Symbol T g.NT)}
  {s : List T}
  (derives : g.Derives' roots <| s.map Symbol.terminal)
  : ∃ _ : Forest g roots s, True := by
    generalize h_size : derives.sizeOf = n
    induction n using Nat.strong_induction_on generalizing derives roots s with
    | h n hi =>
      rcases h_derives : derives
      case refl => use (by apply Forest.ofString s)
      case trans u h_produces child_derives =>
        obtain ⟨ r, hr, p, q, hp, hq ⟩ := Produces.exists_parts h_produces
        have h_decreasing : child_derives.sizeOf < derives.sizeOf := by grind
        revert h_produces child_derives
        rw [hq]
        intro h_produces child_derives h_derives h_decreasing
        obtain ⟨ s', s₃, ⟨ derives', h' ⟩, ⟨ derives₃, h₃ ⟩, hs ⟩ :=
          Derives'.of_append_derives' child_derives
        obtain ⟨ s₁, s₂, ⟨ derives₁, h₁ ⟩, ⟨ derives₂, h₂ ⟩, hs' ⟩ :=
          Derives'.of_append_derives' derives'
        simp only [Derives'.sizeOf_def] at h₁ h₂ h₃ h'
        have h_size₁ : derives₁.sizeOf < n := by
          calc
            derives₁.sizeOf ≤ derives'.sizeOf := by exact h₁
            _ ≤ child_derives.sizeOf := by exact h'
            _ < derives.sizeOf := by exact h_decreasing
            _ = n := by rw [h_size]
        have h_size₂ : derives₂.sizeOf < n := by
          calc
            derives₂.sizeOf ≤ derives'.sizeOf := by exact h₂
            _ ≤ child_derives.sizeOf := by exact h'
            _ < derives.sizeOf := by exact h_decreasing
            _ = n := by rw [h_size]
        have h_size₃ : derives₃.sizeOf < n := by
          calc
            _ ≤ child_derives.sizeOf := by exact h₃
            _ < derives.sizeOf := by exact h_decreasing
            _ = n := by rw [h_size]
        have f₁ := hi derives₁.sizeOf h_size₁ derives₁ rfl |>.choose
        have f₂ := hi derives₂.sizeOf h_size₂ derives₂ rfl |>.choose
        have f₃ := hi derives₃.sizeOf h_size₃ derives₃ rfl |>.choose
        have h_produces : g.StrictProduces r.input r.output := by
          use r
          constructor
          · exact hr
          · rfl
        have tree := Tree.node r.output h_produces f₂
        have f' := Forest.nonterminal r.input tree f₃
        have f := Forest.append f₁ f'
        use (by
          subst_eqs
          rw [List.append_assoc, List.append_assoc]
          rw [@List.cons_append]
          rw [List.nil_append]
          exact f)

theorem Forest.of_derives
  {g : ContextFreeGrammar T} {roots : List (Symbol T g.NT)} {s : List T}
  (h_derives : g.Derives roots <| s.map Symbol.terminal)
  : ∃ _ : Forest g roots s, True := by
    apply Derives'.of_derives at h_derives
    obtain ⟨ derives, - ⟩ := h_derives
    apply Forest.of_derives' at derives
    exact derives

theorem Tree.of_derives
  {g : ContextFreeGrammar T} {n : g.NT} {s : List T}
  (h_derives : g.Derives [.nonterminal n] <| s.map Symbol.terminal)
  : ∃ _ : Tree g n s, True := by
    use Tree.ofForest (Forest.of_derives h_derives).choose

noncomputable def Tree.ofDerives
  (h_derives : g.Derives [.nonterminal n] <| s.map Symbol.terminal) : Tree g n s :=
  Tree.of_derives h_derives |>.choose

noncomputable def Forest.ofDerives
  (h_derives : g.Derives roots <| s.map Symbol.terminal) : Forest g roots s :=
  Forest.of_derives h_derives |>.choose

theorem derives_iff_leftmost_derives
  {s : List T}
  {u : List (Symbol T g.NT)}
  : g.Derives u (s.map Symbol.terminal) ↔ g.DerivesLeftmost u (s.map Symbol.terminal) := by
    constructor
    · intro h_derives
      have f := Forest.ofDerives h_derives
      apply Forest.derives_leftmost_yield f
    · intro h_derives_leftmost
      exact Derives.of_derives_leftmost g h_derives_leftmost

end ContextFreeGrammar
