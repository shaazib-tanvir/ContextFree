import Mathlib.Computability.ContextFreeGrammar
import LeanSearchClient

namespace ContextFreeRule

inductive RewritesLeftmost
  (r : ContextFreeRule T N) : List (Symbol T N) → List (Symbol T N) → Prop
  | head (s : List (Symbol T N)) :
      r.RewritesLeftmost (Symbol.nonterminal r.input :: s) (r.output ++ s)
  | cons (x : T) {s₁ s₂ : List (Symbol T N)} (hrs : RewritesLeftmost r s₁ s₂) :
      r.RewritesLeftmost ((.terminal x) :: s₁) ((.terminal x) :: s₂)

lemma RewritesLeftmost.exists_parts
  {r : ContextFreeRule T N}
  (hr : r.RewritesLeftmost u v) : 
    ∃ (p : List T) (q : List (Symbol T N)),
    u = p.map Symbol.terminal ++ [.nonterminal r.input] ++ q
    ∧ v = p.map Symbol.terminal ++ r.output ++ q := by
      rcases hr with s | ⟨ x, hrs ⟩
      · use []; simp
      · have hi := RewritesLeftmost.exists_parts hrs
        obtain ⟨ p, q, hi ⟩ := hi
        use x :: p; use q
        grind

lemma RewritesLeftmost.input_output
  {r : ContextFreeRule T N} :
    r.RewritesLeftmost [Symbol.nonterminal r.input] r.output := by
    grind [RewritesLeftmost.head]

lemma RewritesLeftmost.of_exists_parts
  {r : ContextFreeRule T N}
  (p : List T) (q u v : List (Symbol T N))
  (hu : u = p.map Symbol.terminal ++ [Symbol.nonterminal r.input] ++ q)
  (hv : v = p.map Symbol.terminal ++ r.output ++ q) :
    r.RewritesLeftmost u v := by
        match p with
        | [] =>
          grind [RewritesLeftmost.head q]
        | a :: as =>
          simp only [List.map_cons, List.cons_append, List.append_assoc, List.nil_append] at hu hv
          generalize hu' :
          (List.map Symbol.terminal as ++ Symbol.nonterminal r.input :: q) = u' at hu
          generalize hv' : (List.map Symbol.terminal as ++ (r.output ++ q)) = v' at hv
          have hi := @RewritesLeftmost.of_exists_parts T N r as q u' v' (by grind) (by grind)
          grind [RewritesLeftmost.cons]

lemma RewritesLeftmost.iff_exists_parts
  {r : ContextFreeRule T N}
  (u v : List (Symbol T N)) :
    r.RewritesLeftmost u v ↔
    ∃ (p : List T) (q : List (Symbol T N)),
    u = p.map Symbol.terminal ++ [Symbol.nonterminal r.input] ++ q ∧
    v = p.map Symbol.terminal ++ r.output ++ q := by
      constructor
      · intro h; apply RewritesLeftmost.exists_parts h
      · rintro ⟨ p, q, ⟨ hu, hv ⟩ ⟩
        apply RewritesLeftmost.of_exists_parts p q u v hu hv

lemma Rewrites.of_rewrites_leftmost
  {r : ContextFreeRule T N}
  (u v : List (Symbol T N))
  (hrl : r.RewritesLeftmost u v) :
    r.Rewrites u v := by
      rw [RewritesLeftmost.iff_exists_parts] at hrl
      rw [rewrites_iff]
      grind

lemma RewritesLeftmost.append_left
  {r : ContextFreeRule T N}
  (hvw : r.RewritesLeftmost u v) (p : List T) :
    r.RewritesLeftmost (p.map Symbol.terminal ++ u) (p.map Symbol.terminal ++ v) := by
      rw [iff_exists_parts] at *
      rcases hvw with ⟨x, y, hxy⟩
      use p ++ x, y
      simp_all

lemma RewritesLeftmost.append_right
  {r : ContextFreeRule T N}
  (hvw : r.RewritesLeftmost u v) (p : List (Symbol T N)) :
    r.RewritesLeftmost (u ++ p) (v ++ p) := by
      rw [iff_exists_parts] at *
      rcases hvw with ⟨x, y, hxy⟩
      use x, y ++ p
      simp_all

lemma RewritesLeftmost.nil_rewrites_of_nil
  {r : ContextFreeRule T N}
  (u : List (Symbol T N))
  (hr : r.RewritesLeftmost [] u) :
    u = [] := by
      match u with
      | [] => simp
      | x :: xs =>
        cases hr

end ContextFreeRule

namespace ContextFreeGrammar

variable (g : ContextFreeGrammar T)

def ProducesLeftmost (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.RewritesLeftmost u v

abbrev DerivesLeftmost (u v : List (Symbol T g.NT)) : Prop :=
  Relation.ReflTransGen g.ProducesLeftmost u v

def GeneratesLeftmost (u : List (Symbol T g.NT)) : Prop :=
  g.Derives [.nonterminal g.initial] u

lemma ProducesLeftmost.nil_produces_of_nil
  (u : List (Symbol T g.NT))
  (h_produces : g.ProducesLeftmost [] u)
  : u = [] := by
    grind only [eq_def, ContextFreeRule.RewritesLeftmost.nil_rewrites_of_nil]

lemma ProducesLeftmost.cons
  (t : T)
  (u v : List (Symbol T g.NT))
  (h_produces : g.ProducesLeftmost u v)
  : g.ProducesLeftmost ((.terminal t) :: u) ((.terminal t) :: v) := by
    unfold ProducesLeftmost at h_produces
    obtain ⟨ r, ⟨ h_r, h_rewrites ⟩ ⟩ := h_produces
    unfold ProducesLeftmost
    use r
    constructor
    · grind
    · apply ContextFreeRule.RewritesLeftmost.cons
      grind

lemma DerivesLeftmost.single
  (u v : List (Symbol T g.NT))
  (h_produces : g.ProducesLeftmost u v)
  : g.DerivesLeftmost u v := by solve_by_elim

lemma DerivesLeftmost.trans
  (u v w : List (Symbol T g.NT))
  (huv : g.DerivesLeftmost u v)
  (hvw : g.DerivesLeftmost v w)
  : g.DerivesLeftmost u w := by
    exact Relation.ReflTransGen.trans huv hvw

lemma DerivesLeftmost.trans_produces
  (u v w : List (Symbol T g.NT))
  (huv : g.DerivesLeftmost u v)
  (hvw : g.ProducesLeftmost v w)
  : g.DerivesLeftmost u w := by
    solve_by_elim

lemma DerivesLeftmost.cons
  (t : T)
  (u v : List (Symbol T g.NT))
  (h_derives : g.DerivesLeftmost u v)
  : g.DerivesLeftmost ((.terminal t) :: u) ((.terminal t) :: v) := by
    induction h_derives
    · grind only [= Relation.reflTransGen_iff_eq_or_transGen]
    · grind only [Relation.ReflTransGen.tail, ProducesLeftmost.cons]

lemma ProducesLeftmost.append_left
  (s : List T)
  (u v : List (Symbol T g.NT))
  (h_produces : g.ProducesLeftmost u v)
  : g.ProducesLeftmost
  (s.map Symbol.terminal ++ u) (s.map Symbol.terminal ++ v) := by
    grind only [eq_def, ContextFreeRule.RewritesLeftmost.append_left]

lemma ProducesLeftmost.append_right
  (u v w : List (Symbol T g.NT))
  (h_produces : g.ProducesLeftmost u v)
  : g.ProducesLeftmost (u ++ w) (v ++ w) := by
    grind only [eq_def, ContextFreeRule.RewritesLeftmost.append_right]

lemma DerivesLeftmost.append_left
  (s : List T)
  (u v : List (Symbol T g.NT))
  (h_derives : g.DerivesLeftmost u v)
  : g.DerivesLeftmost
  (s.map Symbol.terminal ++ u) (s.map Symbol.terminal ++ v) := by
    induction h_derives
    · grind only [= Relation.reflTransGen_iff_eq_or_transGen]
    · grind only [Relation.ReflTransGen.tail, ProducesLeftmost.append_left]

lemma DerivesLeftmost.append_right
  (u v w : List (Symbol T g.NT))
  (h_derives : g.DerivesLeftmost u v)
  : g.DerivesLeftmost (u ++ w) (v ++ w) := by
    induction h_derives with
    | refl =>
      rfl
    | @tail a b h_ua h_produces h_derives =>
      change g.DerivesLeftmost u a at h_ua
      have h_ab : g.ProducesLeftmost (a ++ w) (b ++ w) := by
        exact ProducesLeftmost.append_right g a b w h_produces
      apply DerivesLeftmost.trans
      · exact h_derives
      · grind

lemma DerivesLeftmost.nil_derives_of_nil
  (u : List (Symbol T g.NT))
  (h_derives : g.DerivesLeftmost [] u)
  : u = [] := by
    induction h_derives
    · rfl
    · grind only [ProducesLeftmost.nil_produces_of_nil]

private lemma break_list
  (as bs cs ds : List α)
  (x : α)
  (h : as ++ bs = cs ++ [x] ++ ds)
  : ∃ xs ys : List α,
  as = xs ++ [x] ++ ys ∧ xs = cs ∧ ys ++ bs = ds
  ∨ bs = xs ++ [x] ++ ys ∧ as ++ xs = cs ∧ ys = ds := by
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    induction as generalizing bs cs ds with
    | nil =>
      simp_all
    | cons a as hi =>
      match cs with
      | [] =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        obtain ⟨ hax, h ⟩ := h
        use []
        simp [*]
      | c :: cs =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨ hac, h ⟩ := h
        specialize hi bs cs ds h
        obtain ⟨ xs, ys, hi ⟩ := hi
        rcases hi with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
        · use a :: xs
          use ys
          simp [*]
        · use xs
          use ys
          simp [*]

lemma DerivesLeftmost.exists_parts_of_cons_derives
  (x : Symbol T g.NT)
  (u v : List (Symbol T g.NT))
  (h_derives : g.DerivesLeftmost (x :: u) v)
  : ∃ z w : List (Symbol T g.NT),
  v = z ++ w ∧
  g.DerivesLeftmost [x] z ∧
  g.DerivesLeftmost u w := by
    induction h_derives with
    | refl =>
      use [x]
      use u
      grind
    | @tail a b h_derives h_produces hi =>
      change g.DerivesLeftmost (x :: u) a at h_derives
      obtain ⟨ z, w, ⟨ ha, hxz, huw ⟩ ⟩ := hi
      rw [ha] at h_produces
      unfold ProducesLeftmost at h_produces
      obtain ⟨ r, ⟨ h_r, h_rewrites ⟩ ⟩ := h_produces
      rw [ContextFreeRule.RewritesLeftmost.iff_exists_parts] at h_rewrites
      obtain ⟨ p, q, h_rewrites ⟩ := h_rewrites
      obtain ⟨ hzw, hb ⟩ := h_rewrites
      apply break_list at hzw
      obtain ⟨ xs, ys, hzw ⟩ := hzw
      rcases hzw with ⟨ hz, ⟨ hp, hq ⟩ ⟩ | ⟨ hw, ⟨ hp, hq ⟩ ⟩
      · rw [hp] at hz
        rw [←hq] at hb
        rw [←List.append_assoc] at hb
        use (List.map Symbol.terminal p ++ r.output ++ ys)
        use w
        constructor
        · exact hb
        · constructor
          · apply DerivesLeftmost.trans_produces
            · exact hxz
            ·  grind only [ProducesLeftmost.eq_def,
              ContextFreeRule.RewritesLeftmost.of_exists_parts]
          · exact huw
      · rw [hq] at hw
        rw [←hp] at hb
        have hxs : ∃ zs, xs = List.map Symbol.terminal zs := by
          clear hw hb h_r r huw hxz ha h_derives u v a b w hq q ys x
          induction p generalizing z xs with
          | nil =>
            simp only [List.map_nil, List.append_eq_nil_iff] at hp
            use []
            grind
          | cons x p hi =>
            simp only [List.map_cons] at hp
            match z with
            | [] =>
              simp only [List.nil_append] at hp
              use x :: p
              grind
            | y :: zs =>
              simp only [List.cons_append, List.cons.injEq] at hp
              obtain ⟨ -, hp ⟩ := hp
              specialize hi zs xs hp
              exact hi
        use z
        use xs ++ r.output ++ q
        constructor
        · grind only
        · constructor
          · simp [*]
          · apply DerivesLeftmost.trans_produces
            · exact huw
            · unfold ProducesLeftmost
              use r
              constructor
              · exact h_r
              · rw [ContextFreeRule.RewritesLeftmost.iff_exists_parts]
                obtain ⟨ zs, hxs ⟩ := hxs
                use zs
                use q
                constructor
                · rw [←hxs]; exact hw
                · rw [hxs]

lemma List.map_split_of_split
  {xs : List α}
  {ys zs : List β}
  (f : α → β)
  (hsplit : xs.map f = ys ++ zs)
  : ∃ ys' zs' : List α, ys = ys'.map f ∧ zs = zs'.map f := by
    induction ys generalizing xs zs with
    | nil =>
      simp only [List.nil_eq, List.map_eq_nil_iff, exists_and_left, exists_eq_left]
      simp only [List.nil_append] at hsplit
      use xs; grind
    | cons a as hi =>
      match xs with
      | [] =>
        grind
      | x :: xs =>
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨ ha, hsplit ⟩ := hsplit
        specialize @hi xs zs hsplit
        obtain ⟨ ys', zs', hi ⟩ := hi
        use (x :: ys')
        use zs'
        grind

lemma DerivesLeftmost.append_left_of_derives_terminal
  {p u v : List (Symbol T g.NT)}
  {s : List T}
  (u_derives_v : g.DerivesLeftmost u v)
  (p_derives_s : g.DerivesLeftmost p <| s.map Symbol.terminal)
  : g.DerivesLeftmost (p ++ u) (s.map Symbol.terminal ++ v) := by
    induction p generalizing s with
    | nil =>
      grind only [nil_derives_of_nil]
    | cons x xs hi =>
      simp only [List.cons_append]
      apply exists_parts_of_cons_derives at p_derives_s
      obtain ⟨ z, w, ⟨ hs, hz, hxs ⟩ ⟩ := p_derives_s
      have ⟨ z', w', ⟨ hz', hw' ⟩ ⟩  := List.map_split_of_split _ hs
      specialize @hi w' (by grind)
      rw [←hw'] at hi
      apply DerivesLeftmost.trans
      · suffices g.DerivesLeftmost (x :: (xs ++ u)) (z ++ (xs ++ u)) by rfl
        rw [← @List.singleton_append]
        apply DerivesLeftmost.append_right
        exact hz
      · rw [hs]
        rw [List.append_assoc]
        rw [← @List.singleton_append]
        apply DerivesLeftmost.trans
        · change g.DerivesLeftmost ([x] ++ (xs ++ u)) (z ++ (xs ++ u))
          apply DerivesLeftmost.append_right
          exact hz
        · rw [hz']
          apply DerivesLeftmost.append_left
          exact hi

end ContextFreeGrammar
