import Mathlib.Computability.ContextFreeGrammar

noncomputable def Or.elim_noncomputable
  (h : h₁ ∨ h₂)
  (f₁ : h₁ → α)
  (f₂ : h₂ → α) : α :=
  have h : ∃ a : α, ((x₁ : h₁) → a = f₁ x₁) ∧ ((x₂ : ¬h₁) → a = f₂ (by grind)) := by
    by_cases h' : h₁
    · use f₁ h'
      grind
    · use f₂ (by grind)
      grind
  h.choose

theorem Or.elim_noncomputable_spec
  (h : h₁ ∨ h₂)
  (f₁ : h₁ → α)
  (f₂ : h₂ → α)
  :
  ((x₁ : h₁) → Or.elim_noncomputable h f₁ f₂ = f₁ x₁) ∧
  ((x₂ : ¬h₁) → Or.elim_noncomputable h f₁ f₂ = f₂ (by grind)) := by
    grind [= elim_noncomputable]

mutual
def even : Nat → Bool
  | 0 => true
  | n + 1 => odd n

def odd : Nat → Bool
  | 0 => false
  | n + 1 => even n
end

inductive ParseTree (g : ContextFreeGrammar T) (n : g.NT) where
  | terminal
  (children : List T)
  (h_produces : g.Produces [.nonterminal n] <| children.map Symbol.terminal)
  : ParseTree g n
  | cons
  (children : List (Symbol T g.NT))
  : ParseTree g n

/--/
/- inductive Tree (g : ContextFreeGrammar T) where -/
/-   | terminal : T → Tree g -/
/-   | cons : g.NT → List (Tree g) → Tree g -/
/--/
/- variable {g : ContextFreeGrammar T} -/
/--/
/- def Tree.root (tree : Tree g) : Symbol T g.NT := -/
/-   match tree with -/
/-   | terminal t => .terminal t -/
/-   | cons n _ => .nonterminal n -/
/--/
/- def Tree.leaves (tree : Tree g) : List T := -/
/-   match tree with -/
/-   | terminal t => [t] -/
/-   | cons _ children => -/
/-     children.foldl (fun (x : List T) y => x ++ Tree.leaves y) [] -/
/--/
/- inductive Tree.valid : Tree g → Prop where -/
/-   | terminal (x : T) : Tree.valid (terminal x) -/
/-   | cons -/
/-   (n : g.NT) -/
/-   (children : List (Tree g)) -/
/-   (h_produces : g.StrictProduces n (children.map Tree.root)) -/
/-   (h_valid : ∀ x ∈ children, x.valid) : -/
/-     Tree.valid (Tree.cons n children) -/
/--/
/- @[ext] -/
/- structure ParseTree (g : ContextFreeGrammar T) where -/
/-   tree : Tree g -/
/-   valid : tree.valid -/
/-   root_nonterminal : ∃ n, tree.root = .nonterminal n -/
/--/
/- @[coe] -/
/- def ParseTree.coe_tree (tree : ParseTree g) : Tree g := tree.tree -/
/--/
/- instance ParseTree.instCoeTree : Coe (ParseTree g) (Tree g) where -/
/-   coe := coe_tree -/
/--/
/- lemma ParseTree.coe_valid (tree : ParseTree g) : (tree : Tree g).valid := tree.valid -/
/--/
/- lemma ParseTree.coe_ne_terminal -/
/-   (tree : ParseTree g) -/
/-   (t : T) -/
/-   (h : (tree : Tree g) = .terminal t) : -/
/-     False := by -/
/-       have ⟨ n, h' ⟩ := tree.root_nonterminal -/
/-       grind [= coe_tree.eq_def, = Tree.root.eq_def, = ParseTree.tree.eq_def] -/
/--/
/- def ParseTree.root (tree : ParseTree g) : g.NT := -/
/-   match h : (tree : Tree g) with -/
/-   | .terminal t => -/
/-     have h' : False := ParseTree.coe_ne_terminal tree t h -/
/-     h'.elim -/
/-   | .cons n _ => n -/
/--/
/- def ParseTree.children (tree : ParseTree g) : List (Tree g) := -/
/-   match h : (tree : Tree g) with -/
/-   | .terminal t => -/
/-     have h' : False := ParseTree.coe_ne_terminal tree t h -/
/-     h'.elim -/
/-   | .cons _ children => children -/
/--/
/- lemma ParseTree.children_valid -/
/-   (tree : ParseTree g) -/
/-     : tree.children.Forall Tree.valid := by -/
/-       rw [List.forall_iff_forall_mem] -/
/-       intro x h -/
/-       have h_valid := coe_valid tree -/
/-       generalize h_tree : (tree : Tree g) = t at h_valid -/
/-       induction h_valid with -/
/-       | terminal t' => -/
/-         grind [= children, = coe_tree] -/
/-       | cons n children h_produces h_valid h_valid_ih => -/
/-         grind [children] -/
/--/
/- lemma ParseTree.produces_children -/
/-   (tree : ParseTree g) -/
/-     : g.StrictProduces tree.root (tree.children.map Tree.root) := by -/
/-       have h_valid := coe_valid tree -/
/-       generalize h_tree : (tree : Tree g) = t at * -/
/-       rcases t with t | ⟨ n, children ⟩ -/
/-       · grind [= coe_tree, = StrictProduces, = root, = Tree.root, = children] -/
/-       · unfold ParseTree.children -/
/-         rcases h_valid -/
/-         grind [= coe_tree, = StrictProduces, = Tree.root, = root] -/
/--/
/- def ParseTree.mk' -/
/-   (n : g.NT) -/
/-   (children : List ((ParseTree g) ⊕ T)) -/
/-   (produces : g.StrictProduces n <| children.map fun x => match x with -/
/-   | .inl t => .nonterminal t.root -/
/-   | .inr t => .terminal t) : ParseTree g := -/
/-   { -/
/-     tree := Tree.cons n (children.map fun x => match x with -/
/-       | .inl t => t.tree -/
/-       | .inr t => Tree.terminal t) -/
/-     root_nonterminal := by solve_by_elim -/
/-     valid := by -/
/-       apply Tree.valid.cons -/
/-       · generalize h_children' : (List.map Tree.root -/
/-         (List.map (fun x ↦ match x with -/
/-         | Sum.inl t => t.tree -/
/-         | Sum.inr t => Tree.terminal t) children)) = children' -/
/-         generalize h_children'' : (List.map (fun x ↦ match x with -/
/-         | Sum.inl t => Symbol.nonterminal t.root -/
/-         | Sum.inr t => Symbol.terminal t) children) = children'' at produces -/
/-         have h : children' = children'' := by -/
/-           rw [←h_children', ←h_children''] -/
/-           simp only [List.map_map, List.map_inj_left, Function.comp_apply, Sum.forall] -/
/-           constructor -/
/-           · intro t ht -/
/-             grind only [StrictProduces, root, coe_tree, Tree.root, #9cf5, #80b1] -/
/-           · intro t ht -/
/-             rfl -/
/-         rw [h]; exact produces -/
/-       · intro x hx -/
/-         simp only [List.mem_map, Sum.exists] at hx -/
/-         obtain ⟨ y, ⟨ hy, hy_tree ⟩ ⟩ | ⟨ t, ⟨ h_child, h_terminal ⟩ ⟩ := hx -/
/-         · rw [←hy_tree] -/
/-           exact y.valid -/
/-         · rw [←h_terminal] -/
/-           apply Tree.valid.terminal -/
/-   } -/
/--/
/- lemma ParseTree.induction -/
/-   (p : ParseTree g → Prop) -/
/-   (tree : ParseTree g) -/
/-     : p tree := by -/
/-       sorry -/
/--/
/- lemma List.cons_eq_append -/
/-   (x : α) (xs : List α) : x :: xs = [x] ++ xs := by grind -/
/--/
/- lemma List.foldl_append_eq_append -/
/-   (xs : List α) (ys zs : List β) -/
/-   (f : α → List β) -/
/-     : xs.foldl (fun (x : List β) y => x ++ f y) (ys ++ zs) = -/
/-       ys ++ xs.foldl (fun (x : List β) y => x ++ f y) zs := by simp -/
/--/
/- theorem ParseTree.derives_leftmost_leaves -/
/-   (tree : ParseTree g) -/
/-     : g.DerivesLeftmost [.nonterminal tree.root] ((tree : Tree g).leaves.map Symbol.terminal) := by -/
/-       rcases tree with ⟨ tree, h_valid, h_root ⟩ -/
/-       induction h_valid with -/
/-       | terminal t => -/
/-         grind [= Tree.root, = root, = Tree.leaves, = coe_tree] -/
/-       | cons n children h_produces h_valid h_valid_ih => -/
/-         simp only [ParseTree.root, coe_tree] -/
/-         unfold Tree.leaves -/
/-         induction children generalizing n with -/
/-         | nil => -/
/-           grind only [= List.map_nil, List.foldl_nil, = Relation.reflTransGen_iff_eq_or_transGen, -/
/-             Relation.TransGen.single, StrictProduces.produces_leftmost] -/
/-         | cons x xs h_xs => -/
/-           rw [@List.foldl_cons] -/
/-           rw [List.nil_append, ←List.append_nil x.leaves] -/
/-           rw [List.foldl_append_eq_append xs x.leaves []] -/
/-           rw [@List.map_append] -/
/-           sorry -/
/--/

