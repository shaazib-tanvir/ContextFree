import Mathlib.Tactic.Basic
import Mathlib.Computability.ContextFreeGrammar

namespace ContextFreeRule

variable {r : ContextFreeRule T N}

def StrictRewrites (n : N) (u : List (Symbol T N)) := r = ⟨ n, u ⟩

end ContextFreeRule

@[grind .]
lemma list_symbol_split
  {s : List T}
  {u v : List (Symbol T N)}
  (h : u ++ v = List.map Symbol.terminal s)
  : ∃ u' v',
    u = List.map Symbol.terminal u' ∧
    v = List.map Symbol.terminal v' ∧
    u' ++ v' = s := by
      induction s generalizing u v with
      | nil =>
        simp_all
      | cons t ts hi =>
        simp_all only [exists_and_left, List.map_cons]
        match u with
        | [] => simp_all
        | t' :: u' =>
          simp_all only [List.cons_append, List.cons.injEq]
          obtain ⟨ ht', hts ⟩ := h
          subst_eqs
          specialize @hi u' v hts
          obtain ⟨ w, ⟨ hw, ⟨ x, hx, hts' ⟩ ⟩ ⟩ := hi
          subst_eqs
          use (t :: w)
          constructor
          · rfl
          · use x
            constructor
            · rfl
            · simp

namespace ContextFreeGrammar

def StrictProduces (g : ContextFreeGrammar T) (n : g.NT) (u : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.StrictRewrites n u

variable {g : ContextFreeGrammar T}

lemma Produces.exists_parts
  {u v : List (Symbol T g.NT)}
  (huv : g.Produces u v)
  : ∃ r ∈ g.rules, ∃ p q : List (Symbol T g.NT),
  u = p ++ [.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
    unfold Produces at huv
    obtain ⟨ r, hr, huv ⟩ := huv
    apply ContextFreeRule.Rewrites.exists_parts at huv
    grind

lemma Produces.nil_of_nil_produces
  {u : List (Symbol T g.NT)}
  (h_produces : g.Produces [] u)
  : u = [] := by
    obtain ⟨ r, hr, p, q, hp, hq ⟩ := Produces.exists_parts h_produces
    cases p <;> cases q <;> cases r.output <;> grind

lemma Produces.of_produces_nil
  {u : List (Symbol T g.NT)}
  (h_produces : g.Produces u [])
  : ∃ n : g.NT, u = [.nonterminal n] ∧ g.StrictProduces n [] := by
    apply Produces.exists_parts at h_produces
    obtain ⟨ r, hr, p, q, hp, hq ⟩ := h_produces
    use r.input
    simp_all only [List.append_assoc, List.cons_append, List.nil_eq, List.append_eq_nil_iff,
      List.append_nil, List.nil_append, true_and]
    use r; constructor
    · exact hr
    · ext <;> simp_all

lemma Produces.of_terminal_cons_produces
  {t : T}
  {u v : List (Symbol T g.NT)}
  (h_produces : g.Produces (.terminal t :: u) v)
  : ∃ v', g.Produces u v' ∧ v = (.terminal t) :: v' := by
    apply Produces.exists_parts at h_produces
    obtain ⟨ r, hr, p, q, hp, hq ⟩ := h_produces
    rcases p with  _ | ⟨ x, xs ⟩ <;> try grind
    subst_vars
    rcases x with t' | n <;> try grind
    simp_all only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq,
      Symbol.terminal.injEq, true_and, exists_eq_right']
    obtain ⟨ ht, hxs ⟩ := hp
    subst_vars
    use r
    constructor
    · exact hr
    · rw [@List.append_cons]
      rw [←@List.append_assoc]
      apply ContextFreeRule.rewrites_of_exists_parts

lemma Produces.of_nonterminal_cons_produces
  {n : g.NT}
  {xs ys : List (Symbol T g.NT)}
  (h_produces : g.Produces (.nonterminal n :: xs) ys)
  : (∃ zs, g.StrictProduces n zs ∧ ys = zs ++ xs) ∨
    (∃ zs, g.Produces xs zs ∧ ys = (.nonterminal n) :: zs) := by
      apply Produces.exists_parts at h_produces
      obtain ⟨ r, hr, p, q, hp, hq ⟩ := h_produces
      match p with
      | [] =>
        simp_all only [List.nil_append, List.cons_append, List.cons.injEq, Symbol.nonterminal.injEq,
          List.append_cancel_right_eq, exists_eq_right']
        subst_vars
        left; solve_by_elim
      | n' :: p' =>
        simp_all only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq,
          true_and, exists_eq_right']
        obtain ⟨ hn, hxs ⟩ := hp
        subst_vars; right
        rw [@List.append_cons]
        rw [← @List.append_assoc]
        use r
        constructor
        · exact hr
        · apply ContextFreeRule.rewrites_of_exists_parts

lemma Derives.produces_trans
  (u v w : List (Symbol T g.NT))
  (huv : g.Produces u v)
  (hvw : g.Derives v w)
  : g.Derives u w := by exact Relation.ReflTransGen.head huv hvw

lemma Derives.nil_of_nil_derives
  {u : List (Symbol T g.NT)}
  (h_derives : g.Derives [] u)
  : u = [] := by
    induction h_derives
    · grind
    · grind only [Produces.nil_of_nil_produces]

lemma Derives.of_cons_terminal_derives
  {s : List T}
  {u : List (Symbol T g.NT)}
  {t : T}
  (h_derives : g.Derives ((.terminal t) :: u) (s.map Symbol.terminal))
  : ∃ s' : List T, g.Derives u (List.map Symbol.terminal s') ∧ s = t :: s' := by
    generalize hv : (Symbol.terminal t) :: u = v at *
    generalize hw : s.map Symbol.terminal = w at *
    induction h_derives using Relation.ReflTransGen.head_induction_on generalizing s t u with
    | refl =>
      match _ : s with
      | [] => simp_all
      | t' :: s' => grind
    | @head x y hxw hyw hi =>
      change g.Derives y w at hyw
      unfold Produces at hxw
      obtain ⟨ r, hr, hxy ⟩ := hxw
      apply ContextFreeRule.Rewrites.exists_parts at hxy
      obtain ⟨ p, q, hxy ⟩ := hxy
      rw [←hv] at hxy
      have hp : ∃ p', p = Symbol.terminal t :: p' := by
        match p with
        | .nil => grind
        | .cons t' p' =>
          use p'; grind
      obtain ⟨ htu, hy ⟩ := hxy
      obtain ⟨ p', hp ⟩ := hp
      rw [hp] at hy
      specialize @hi s (p' ++ r.output ++ q) t (by grind) (by grind)
      obtain ⟨ s', hi ⟩ := hi
      rw [hp] at htu
      simp at htu
      use s'
      constructor
      · apply Derives.produces_trans
        · have h : g.Produces u (p' ++ r.output ++ q) := by
            use r;
            grind only [ContextFreeRule.rewrites_iff, usr List.append_assoc, = List.cons_append]
          exact h
        · grind
      · grind

lemma Derives.of_app_derives
  {xs ys : List (Symbol T g.NT)}
  {s : List T}
  (h_derives : g.Derives (xs ++ ys) (List.map Symbol.terminal s))
  : ∃ zs ws : List T,
  g.Derives xs (List.map Symbol.terminal zs) ∧
  g.Derives ys (List.map Symbol.terminal ws) ∧
  s = zs ++ ws := by
    generalize hu : xs ++ ys = u at h_derives
    generalize hs' : List.map Symbol.terminal s = s' at h_derives
    induction h_derives using Relation.ReflTransGen.head_induction_on generalizing xs ys with
    | refl =>
      subst_eqs
      obtain ⟨ zs, ws, hxs, hys, hs ⟩ := list_symbol_split hu
      use zs; use ws
      constructor
      · grind only [= Relation.reflTransGen_iff_eq_or_transGen]
      · constructor
        · grind only [= Relation.reflTransGen_iff_eq_or_transGen]
        · exact hs.symm
    | @head as bs h_produces h_derives hi =>
      subst_eqs
      change g.Derives bs (List.map Symbol.terminal s) at h_derives
      apply Produces.exists_parts at h_produces
      obtain ⟨ r, hr, p, q, hp, hq ⟩ := h_produces; subst_eqs
      rw [List.append_eq_append_iff] at hp
      obtain ⟨ cs, hp, hq ⟩ | ⟨ cs, hp, hq ⟩ := hp
      · rw [List.append_eq_append_iff] at hp
        obtain ⟨ ds, hxs, hri ⟩ | ⟨ ds, hp, hcs ⟩ := hp
        · subst_eqs
          cases ds <;> try simp_all only [List.append_assoc, exists_and_left, List.nil_append,
            List.append_nil]
          case nil =>
              subst_eqs
              specialize @hi p (r.output ++ q) (by rfl)
              obtain ⟨ zs, hp_derives, xs, hrq_derives, hs ⟩ := hi
              subst_eqs
              use zs
              constructor
              · exact hp_derives
              · use xs
                simp only [List.cons_append, List.nil_append, and_true]
                apply Derives.produces_trans
                · change g.Produces ([.nonterminal r.input] ++ q) (r.output ++ q) 
                  use r
                  constructor
                  · exact hr
                  · solve_by_elim
                · exact hrq_derives
          case cons d ds =>
            simp_all only [List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff,
              List.nil_append]
            obtain ⟨ hri, hds, hcs ⟩ := hri
            subst_eqs
            specialize @hi (p ++ r.output) q (by simp)
            obtain ⟨ xs, hpr, ⟨ ys, hq, hs ⟩ ⟩ := hi
            subst_eqs
            use xs
            constructor
            · apply Derives.produces_trans
              · change g.Produces (p ++ [.nonterminal r.input]) (p ++ r.output)
                use r
                constructor
                · exact hr
                · rw [←List.append_nil (p ++ r.output)]
                  rw [←List.append_nil (p ++ [Symbol.nonterminal r.input])]
                  grind only [ContextFreeRule.rewrites_of_exists_parts]
              · exact hpr
            · use ys
        · specialize @hi xs (ds ++ r.output ++ q) (by grind)
          simp_all only [List.append_assoc, List.cons_append, List.nil_append, exists_and_left]
          subst_eqs
          obtain ⟨ zs, hxs, ⟨ ws, hdsrq, hs ⟩ ⟩ := hi
          use zs
          constructor
          · exact hxs
          · use ws
            subst_eqs
            simp only [and_true]
            apply Derives.produces_trans
            · rw [@List.append_cons]
              change g.Produces (ds ++ [.nonterminal r.input] ++ q) (ds ++ (r.output ++ q))
              use r
              grind only [usr List.append_assoc, ContextFreeRule.rewrites_iff]
            · apply hdsrq
      · subst_eqs
        simp_all only [List.append_assoc, exists_and_left, List.cons_append, List.nil_append]
        specialize @hi (p ++ r.output ++ cs) ys (by grind)
        obtain ⟨ zs, hzs, ⟨ ws, hws, hs ⟩ ⟩ := hi
        subst_eqs
        use zs
        constructor
        · rw [@List.append_cons]
          apply Derives.produces_trans
          · change g.Produces (p ++ [Symbol.nonterminal r.input] ++ cs) (p ++ r.output ++ cs)
            use r
            grind only [ContextFreeRule.rewrites_of_exists_parts]
          · apply hzs
        · use ws

end ContextFreeGrammar
