import Mathlib.Computability.ContextFreeGrammar
import ContextFree.LeftmostDerivation
import ContextFree.Basic
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

variable {g : ContextFreeGrammar T}

inductive Tree (g : ContextFreeGrammar T) where
  | terminal (t : T) : Tree g
  | nonterminal (n : g.NT) (children : List (Tree g)) : Tree g

def Tree.root (tree : Tree g) : Symbol T g.NT :=
  match tree with
  | .terminal t => .terminal t
  | .nonterminal n _ => .nonterminal n

def Tree.root_nonterminal (tree : Tree g) : Prop :=
  match tree.root with
  | .terminal _ => False
  | .nonterminal _ => True

lemma Tree.root_nonterminal_iff
  (tree : Tree g)
  : tree.root_nonterminal ↔
  ∃ n : g.NT, ∃ children : List (Tree g), tree = nonterminal n children := by
    unfold Tree.root_nonterminal; unfold Tree.root
    grind

def Tree.sizeOf (tree : Tree g) : Nat :=
  match tree with
  | .terminal _ => 0
  | .nonterminal n children =>
    1 + (children.map (fun c => c.sizeOf) |>.sum)

instance Tree.instSizeOf : SizeOf (Tree g) where
  sizeOf := sizeOf

def Tree.children
  (tree : Tree g)
  : List (Symbol T g.NT) :=
  match tree with
  | .terminal _ => []
  | .nonterminal _ children => children.map root

inductive Tree.StrictProduces : (Tree g) → Prop where
  | terminal
  (t : T)
  : StrictProduces (Tree.terminal t)
  | nonterminal 
  (n : g.NT)
  (children : List (Tree g))
  (h_produces : g.StrictProduces n (children.map Tree.root))
  (h_children : ∀ t ∈ children, t.StrictProduces)
  : StrictProduces (Tree.nonterminal n children)

def Tree.well_formed (tree : Tree g) : Prop :=
  tree.root_nonterminal ∧ tree.StrictProduces

lemma Tree.strict_produces_of_well_formed
  (tree : Tree g)
  (h_wf : tree.well_formed)
  : tree.StrictProduces := by grind [= well_formed]

lemma Tree.root_nonterminal_of_well_formed
  (tree : Tree g)
  (h_wf : tree.well_formed)
  : tree.root_nonterminal := by grind [= well_formed]

lemma Tree.of_mem_children
  (tree : Tree g)
  (child : Symbol T g.NT)
  (h_child : child ∈ tree.children)
  : ∃ n, ∃ children, tree = Tree.nonterminal n children := by
    unfold children at h_child
    cases tree with grind

lemma Tree.sizeOf_child_decreasing
  (n : g.NT)
  (children : List (Tree g))
  (child : Tree g)
  (h_child : child ∈ children)
  : (Tree.nonterminal n children).sizeOf > child.sizeOf := by
    conv =>
      lhs
      unfold sizeOf
    induction children generalizing child n with
    | nil => grind
    | cons x xs hi =>
      simp only [List.map_cons, List.sum_cons]
      simp only [List.mem_cons] at h_child
      rcases h_child with h_child | h_child <;> try grind
      specialize hi n child h_child; grind only

lemma Tree.induction
  (tree : Tree g)
  (p : Tree g → Prop)
  (h_terminal : ∀ t : T, p (Tree.terminal t))
  (h_nonterminal : ∀ n : g.NT, ∀ children : List (Tree g),
  (children.Forall p) → p (Tree.nonterminal n children))
  : p tree := by
    apply Tree.rec
    · exact h_terminal
    · intro n children h
      change children.Forall p at h
      solve_by_elim
    · simp
    · intro head tail h_head h_tail
      simp [*]

def ParseTree (g : ContextFreeGrammar T) := {tree : Tree g // tree.well_formed}

def ParseTree.children_trees (tree : ParseTree g) : List (Tree g) :=
  match _ : tree.val with
  | .terminal _ => by solve_by_elim
  | .nonterminal n children => children

lemma ParseTree.mem_children_trees_iff
  (tree : ParseTree g)
  (child : Tree g)
  :
  child ∈ tree.children_trees ↔
  ∃ n children, tree.val = Tree.nonterminal n children ∧ child ∈ children := by
    grind [= ParseTree, = children_trees]

def ParseTree.root (tree : ParseTree g) : g.NT :=
  match _ : tree.val with
  | .terminal t =>
    by
      grind only [usr Subtype.property, Tree.well_formed, Tree.root_nonterminal, Tree.root]
  | .nonterminal n _ => n

def ParseTree.sizeOf (tree : ParseTree g) : Nat := tree.val.sizeOf

instance ParseTree.instSizeOf : SizeOf (ParseTree g) where
  sizeOf := sizeOf

lemma ParseTree.of_nonterminal_child
  (tree : ParseTree g)
  (child : g.NT)
  (h_child : (.nonterminal child) ∈ tree.val.children)
  : ∃ child_tree : ParseTree g, child_tree.root = child ∧ child_tree.val ∈ tree.children_trees := by
    unfold Tree.children at h_child
    have h_tree := Tree.of_mem_children tree.val (.nonterminal child) h_child
    obtain ⟨ n, children, h_tree ⟩ := h_tree
    have h_wf := tree.prop
    have h_strict_produces := Tree.strict_produces_of_well_formed tree.val h_wf
    generalize h_val : tree.val = t at h_strict_produces
    rcases h_strict_produces with t | ⟨ n', children', h_produces, h_strict ⟩
    · grind
    · have h_children' : children' = children := by grind
      rw [h_children'] at h_strict
      rw [h_tree] at h_child; simp only [List.mem_map] at h_child
      obtain ⟨ c, ⟨ h_c, h_child ⟩ ⟩ := h_child
      specialize h_strict c h_c
      have h_nonterminal : c.root_nonterminal := by
        grind only [Tree.root_nonterminal]
      have h_c_wf : c.well_formed := ⟨ h_nonterminal, h_strict ⟩
      let child_tree : ParseTree g := ⟨ c, h_c_wf ⟩
      use child_tree
      grind only [children_trees, StrictProduces, root, Tree.root, #2757, #1195]

noncomputable def ParseTree.ofChild
  (tree : ParseTree g)
  (child : g.NT)
  (h_child : (.nonterminal child) ∈ tree.val.children)
  : ParseTree g := by
    let child_tree := of_nonterminal_child tree child h_child
    exact child_tree.choose

lemma ParseTree.ofChild.val
  (tree : ParseTree g)
  (child : g.NT)
  (h_child : (.nonterminal child) ∈ tree.val.children)
  : (tree.ofChild child h_child).val ∈ tree.children_trees := by
    grind [= ParseTree, = Tree.children, = children_trees, = ofChild]

lemma ParseTree.ofChild.root
  (tree : ParseTree g)
  (child : g.NT)
  (h_child : (.nonterminal child) ∈ tree.val.children)
  : (tree.ofChild child h_child).root = child := by
    grind [= ParseTree, = Tree.children, = ParseTree.root, = ofChild]

lemma ParseTree.ofChild.sizeOf_decreasing
  (tree : ParseTree g)
  (child : g.NT)
  (h_child : (.nonterminal child) ∈ tree.val.children)
  : sizeOf (tree.ofChild child h_child) < sizeOf tree := by
    have h_child_tree := ofChild.val tree child h_child
    conv =>
      lhs; unfold sizeOf
    rw [mem_children_trees_iff] at h_child_tree
    obtain ⟨ n, chidren, ⟨ h_tree, h_child' ⟩ ⟩ := h_child_tree
    generalize h : (tree.ofChild child h_child).val = child' at h_child'
    · fun_induction Tree.sizeOf
      · grind [= ParseTree, = Tree.children, = ofChild, = Tree.sizeOf, = sizeOf]
      · grind =>
          instantiate only [sizeOf.eq_def, Tree.sizeOf]
          instantiate only [Tree.sizeOf_child_decreasing]

inductive Node (g : ContextFreeGrammar T) where
  | tree : ParseTree g → Node g
  | terminal : T → Node g

def Node.symbol (node : Node g) : Symbol T g.NT :=
  match node with
  | .tree t => .nonterminal t.root
  | .terminal t => .terminal t

noncomputable def ParseTree.children (tree : ParseTree g) : List (Node g) :=
  tree.val.children.map_mem fun c h_child => match hc : c with
  | .nonterminal n => .tree <| ParseTree.ofChild tree n (by grind)
  | .terminal t => .terminal t

lemma ParseTree.nonterminal_mem_children
  (tree : ParseTree g)
  (child_tree : ParseTree g)
  (h_child : (.tree child_tree) ∈ tree.children)
  : (.nonterminal child_tree.root) ∈ tree.val.children := by
    unfold children at h_child
    rw [List.mem_map_mem_iff] at h_child
    obtain ⟨ n, _, h_child ⟩ := h_child
    rcases n <;> grind only [ofChild, usr Exists.choose_spec]

noncomputable def ParseTree.childrenNonterminal (tree : ParseTree g) : List (ParseTree g) :=
  tree.children.filterMap
  fun node => match node with
  | .tree t => .some t
  | .terminal _ => .none

lemma ParseTree.mem_childrenNonterminal_iff_tree_mem_children
  (tree : ParseTree g)
  (child : ParseTree g)
  : child ∈ tree.childrenNonterminal ↔ (.tree child) ∈ tree.children := by
    grind [= ParseTree, = childrenNonterminal, = children]

lemma ParseTree.mem_childrenNonterminal_lt_sizeOf_parent
  (tree : ParseTree g)
  (child : ParseTree g)
  (h_child : child ∈ tree.childrenNonterminal)
  : child.sizeOf < tree.sizeOf := by
    unfold childrenNonterminal at h_child
    simp only [List.mem_filterMap] at h_child
    obtain ⟨ c, ⟨ h_c, h_child ⟩ ⟩ := h_child
    rcases c with c | _
    · simp_all only [Option.some.injEq]
      simp only [children, List.mem_pmap] at h_c
      obtain ⟨ n, h, h_c ⟩ := h_c
      rcases n with t | n
      · simp_all
      · simp_all only [Node.tree.injEq]
        rw [←h_c]
        apply ParseTree.ofChild.sizeOf_decreasing
    · grind

theorem ParseTree.induction
  (tree : ParseTree g)
  (p : ParseTree g → Prop)
  (h_ind : ∀ tree : ParseTree g, (∀ child ∈ tree.childrenNonterminal, p child) → p tree)
  : p tree := by
    let children := tree.childrenNonterminal
    have h_children_p : ∀ child ∈ children, p child := by
      intro child h_child
      have h_decreasing : child.sizeOf < tree.sizeOf := by
        exact mem_childrenNonterminal_lt_sizeOf_parent tree child h_child
      apply ParseTree.induction child p h_ind
    specialize h_ind tree h_children_p
    exact h_ind

noncomputable def ParseTree.yield (tree : ParseTree g) : List T :=
  tree.children.attach.flatMap fun c => match hc : c.val with
  | .terminal t => [t]
  | .tree t =>
    have h_decreasing : SizeOf.sizeOf t < SizeOf.sizeOf tree:= by
      have h_mem := c.prop
      rw [hc] at h_mem
      rw [←ParseTree.mem_childrenNonterminal_iff_tree_mem_children tree] at h_mem
      apply mem_childrenNonterminal_lt_sizeOf_parent
      exact h_mem
    ParseTree.yield t

private lemma ParseTree.yield_eq_flatMap_children_yield'
  (tree : ParseTree g)
  : tree.yield = tree.children.attach.unattach.flatMap fun c => match c with
  | .terminal t => [t]
  | .tree t => t.yield := by
    conv =>
      lhs; unfold yield
    generalize h_children : tree.children.attach = children
    induction children with
    | nil => rfl
    | cons c cs hi =>
      grind only [List.flatMap_subtype, #0564, #7ce4, #96f9]

lemma ParseTree.yield_eq_flatMap_children_yield
  (tree : ParseTree g) : tree.yield = tree.children.flatMap fun c => match c with
  | .terminal t => [t]
  | .tree t => t.yield := by
    have h := ParseTree.yield_eq_flatMap_children_yield' tree
    conv at h =>
      rw [List.unattach_attach]
    exact h

lemma ParseTree.root_produces_leftmost_children
  (tree : ParseTree g)
  : g.ProducesLeftmost [.nonterminal tree.root] <| tree.children.map Node.symbol := by
    sorry

lemma ParseTree.root_derives_leftmost_yield
  (tree : ParseTree g)
  : g.DerivesLeftmost [.nonterminal tree.root] <| tree.yield.map Symbol.terminal := by
    apply ParseTree.induction tree
    clear tree
    intro tree h_child
    apply DerivesLeftmost.produces_trans
    · suffices h : 
    g.ProducesLeftmost [Symbol.nonterminal tree.root] (tree.children.map Node.symbol) by
        exact h
      apply ParseTree.root_produces_leftmost_children
    · sorry

end ContextFreeGrammar
