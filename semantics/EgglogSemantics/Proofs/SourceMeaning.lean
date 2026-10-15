import EgglogSemantics.Proofs.SameMeaning
import EgglogSemantics.Proofs.EnvTransform

/-! Ordering-free source evaluation and matching respect inferred constructor facts. -/

namespace Egglog.SourceMeaning

open InferredFacts

/-- Each original binding has a represented counterpart under the same variable. -/
def EnvRelated (d : Database) (σ τ : Env) : Prop :=
  ∀ v t, Env.lookup v σ = some t →
    ∃ u, Env.lookup v τ = some u ∧ u.IsValue d.sig ∧ d.Infers t u

mutual

/-- Constructor syntax respects equal interpreted variable values. This statement
also handles expressions whose result has not been represented yet. -/
theorem eval_interpret {d : Database} {sig : Signature} {σ τ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t →
      ∃ u, Env.lookup v τ = some u ∧ u.IsValue sig ∧ interpret d t = interpret d u) :
    ∀ (e : Expr) {t : Term}, e.OrderingFree → e.eval sig σ = some t →
      ∃ u, e.eval sig τ = some u ∧ interpret d t = interpret d u
  | .lit l, t, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨.lit l, rfl, rfl⟩
  | .var v, t, _, he => by
      obtain ⟨u, hu, hv, hi⟩ := hσ v t (Option.filter_eq_some_iff.mp he).1
      exact ⟨u, Option.filter_eq_some_iff.mpr ⟨hu, hv⟩, hi⟩
  | .app f args, t, hn, he => by
      simp only [Expr.eval] at he
      split at he
      next hc =>
        obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
        obtain ⟨us, hus, hi⟩ := evalList_interpret hσ args hn hts
        refine ⟨.app f us, ?_, congrArg (interpretApp d f) hi⟩
        simp only [Expr.eval, if_pos hc, hus, Option.map_some]
      next => cases he
  | .min _ _, _, hn, _ => by simp [Expr.OrderingFree, Expr.hasMin] at hn

theorem evalList_interpret {d : Database} {sig : Signature} {σ τ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t →
      ∃ u, Env.lookup v τ = some u ∧ u.IsValue sig ∧ interpret d t = interpret d u) :
    ∀ (es : List Expr) {ts : List Term}, Expr.OrderingFreeList es →
      Expr.evalList sig es σ = some ts →
      ∃ us, Expr.evalList sig es τ = some us ∧ interpretList d ts = interpretList d us
  | [], ts, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨[], rfl, rfl⟩
  | e :: es, ts, hn, he => by
      have hn' : e.OrderingFree ∧ Expr.OrderingFreeList es := by
        simpa [Expr.OrderingFreeList, Expr.hasMinList, Expr.OrderingFree] using hn
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain ⟨u, hu, hi⟩ := eval_interpret hσ e hn'.1 ht
      obtain ⟨us, hus, his⟩ := evalList_interpret hσ es hn'.2 hts
      exact ⟨u :: us, by simp [Expr.evalList, hu, hus], congrArg₂ List.cons hi his⟩

end

theorem EnvRelated.mono {d e : Database} {σ τ : Env} (h : EnvRelated d σ τ)
    (hc : d.Contained e) (hs : d.sig = e.sig) : EnvRelated e σ τ := by
  intro v t ht
  obtain ⟨u, hu, hv, hi⟩ := h v t ht
  exact ⟨u, hu, hs ▸ hv, infers_mono hc hi⟩

theorem EnvRelated.interpret {d : Database} (hw : d.WF) {σ τ : Env}
    (h : EnvRelated d σ τ) : ∀ v t, Env.lookup v σ = some t →
      ∃ u, Env.lookup v τ = some u ∧ u.IsValue d.sig ∧ interpret d t = interpret d u := by
  intro v t ht
  obtain ⟨u, hu, hv, hi⟩ := h v t ht
  obtain ⟨w, _, hti, hui⟩ := (infers_iff_interpret hw).mp hi
  exact ⟨u, hu, hv, hti.trans hui.symm⟩

/-- The same constructor expression evaluated at related bindings yields
hypothetically congruent terms, even before either output is recorded. -/
theorem eval_congOn {d : Database} (hw : d.WF) {σ τ : Env}
    (hσ : EnvRelated d σ τ) {e : Expr} {t : Term}
    (hn : e.OrderingFree) (he : e.eval d.sig σ = some t) :
    ∃ u, e.eval d.sig τ = some u ∧ CongOn d [t, u] t u := by
  obtain ⟨u, hu, _⟩ := eval_interpret (hσ.interpret hw) e hn he
  let D := d.withOperands [t, u]
  have hD : D.WF := hw.addTerms [t, u]
  have hσ' := hσ.mono (Database.Contained.addTerms [t, u] d) rfl
  obtain ⟨u', hu', hi⟩ := eval_interpret (hσ'.interpret hD) e hn he
  obtain rfl := Option.some.inj (hu.symm.trans hu')
  have htD : t ∈ D.terms := Database.mem_addTerms (by simp)
  have huD : u ∈ D.terms := Database.mem_addTerms (by simp)
  refine ⟨u, hu, (infers_iff_cong_of_held hD htD huD).mp ?_⟩
  exact (infers_iff_interpret hD).mpr
    ⟨t, htD, interpret_of_held hD t htD,
      hi.symm.trans (interpret_of_held hD t htD)⟩

theorem entry_none_of_allConstructors {sig : Signature} (hc : sig.AllConstructors)
    (e : Expr) : e.entry sig = none := by
  cases e with
  | lit => rfl
  | var => rfl
  | min => rfl
  | app f args =>
      cases hd : sig f with
      | none => simp [Expr.entry, hd]
      | some decl =>
          have hm : decl.merge = none := by simpa [Signature.mergeOf, hd] using hc f
          simp [Expr.entry, hd, hm]

/-- Matching constructor patterns transfers to any consistently chosen represented
bindings. Current-table patterns are excluded by the source signature premise. -/
theorem matches_transport {d e : Database} (hd : d.WF) (he : e.WF)
    (hc : d.sig.AllConstructors) (h : d.SameMeaning e) {σ τ : Env}
    (hσ : EnvRelated e σ τ) {p : Pattern} (hn : p.OrderingFree)
    (hm : Matches d p σ) : Matches e p τ := by
  have hc' : e.sig.AllConstructors := h.sig ▸ hc
  cases hm with
  | @expr exp _ w t hw hval hcong =>
      rw [Expr.evalAtom_eq_eval hc] at hval
      have ht : d.Infers t t :=
        infers_right hd (infers_of_congOn hd (infers_of_held hw) hcong)
      obtain ⟨u, hu, hi⟩ := eval_interpret (hσ.interpret he) exp hn (h.sig ▸ hval)
      obtain ⟨w', hw', hti, _⟩ := (infers_iff_interpret he).mp ((h.inferred _ _).mp ht)
      exact .expr hw' (Expr.evalAtom_of_eval hu)
        (congOn_of_interpret he u hw' (hi.symm.trans hti)).symm
  | @eq a b _ w ta tb hw hva hvb hwa hab =>
      obtain ⟨ua, hua, hia⟩ := eval_interpret (hσ.interpret he) a hn.1 (h.sig ▸ hva)
      obtain ⟨ub, hub, hib⟩ := eval_interpret (hσ.interpret he) b hn.2 (h.sig ▸ hvb)
      have hti := (h.inferred ta tb).mp ⟨w, hw, hwa, hab⟩
      obtain ⟨w', hw', hai, hbi⟩ := (infers_iff_interpret he).mp hti
      obtain ⟨v, hv, hva', hvb'⟩ := (infers_iff_interpret he).mpr
        ⟨w', hw', hia.symm.trans hai, hib.symm.trans hbi⟩
      exact .eq hv hua hub hva' hvb'

open Classical in
/-- Choose one recorded representative for each inferred class. -/
noncomputable def representative (d : Database) (hw : d.WF) (t : Term) : Term :=
  if h : d.Infers t t then ((infers_iff_interpret hw).mp h).choose else t

theorem representative_spec {d : Database} (hw : d.WF) (hs : d.StoreOk) {t : Term}
    (hv : t.IsValue d.sig) (ht : d.Infers t t) :
    representative d hw t ∈ d.values ∧ d.Infers t (representative d hw t) := by
  simp only [representative, dif_pos ht]
  have hr := ((infers_iff_interpret hw).mp ht).choose_spec
  have hi : d.Infers t (((infers_iff_interpret hw).mp ht).choose) :=
    (infers_iff_interpret hw).mpr
      ⟨_, hr.1, hr.2.1, interpret_of_held hw _ hr.1⟩
  have hc := congOn_of_interpret hw t hr.1 hr.2.1
  have hstore : (d.withOperands [t]).StoreOk := hs.addTerm t (Or.inl hv)
  exact ⟨⟨hr.1, (hc.isValue_iff hstore).mp hv⟩, hi⟩

theorem envRelated_map {d e : Database} {σ : Env} {w : Term → Term}
    (hs : ∀ b ∈ σ, b.2 ∈ d.values)
    (hw : ∀ t ∈ d.values, (w t).IsValue e.sig ∧ e.Infers t (w t)) :
    EnvRelated e σ (Env.mapVals w σ) := by
  intro v t ht
  refine ⟨w t, ?_, hw t (hs (v, t) (Env.mem_of_lookup ht))⟩
  simp [lookup_mapVals, ht]

theorem validSubst_map {d e : Database} (hd : d.WF) (he : e.WF)
    (hc : d.sig.AllConstructors) (h : d.SameMeaning e) {w : Term → Term}
    (hw : ∀ t ∈ d.values, w t ∈ e.values ∧ e.Infers t (w t))
    {p : Pattern} {σ : Env} (hn : p.OrderingFree) (hs : ValidSubst d p σ) :
    ValidSubst e p (Env.mapVals w σ) := by
  refine ⟨⟨?_, ?_⟩, matches_transport hd he hc h
    (envRelated_map hs.1.2 (fun t ht => ⟨(hw t ht).1.2, (hw t ht).2⟩)) hn hs.2⟩
  · simpa [dom_mapVals] using hs.1.1
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
    exact (hw _ (hs.1.2 a ha)).1

theorem union2_map (w : Term → Term) {σ τ ρ : Env} (h : Env.Union2 σ τ ρ) :
    Env.Union2 (Env.mapVals w σ) (Env.mapVals w τ) (Env.mapVals w ρ) := by
  refine ⟨?_, by rw [h.2, mapVals_append]⟩
  intro b hb t ht
  obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
  rw [lookup_mapVals] at ht
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact congrArg w (h.1 a ha u hu)

theorem unionAll_map (w : Term → Term) {σs : List Env} {σ : Env}
    (h : Env.UnionAll σs σ) :
    Env.UnionAll (σs.map (Env.mapVals w)) (Env.mapVals w σ) := by
  induction h with
  | nil => exact .nil
  | single σ => exact .single _
  | step h _ ih => exact .step (union2_map w h) ih

theorem validQuerySubst_map {d e : Database} (hd : d.WF) (he : e.WF)
    (hc : d.sig.AllConstructors) (h : d.SameMeaning e) {w : Term → Term}
    (hw : ∀ t ∈ d.values, w t ∈ e.values ∧ e.Infers t (w t))
    {q : Query} {σ : Env} (hn : ∀ p ∈ q, p.OrderingFree)
    (hs : ValidQuerySubst d q σ) : ValidQuerySubst e q (Env.mapVals w σ) := by
  obtain ⟨σs, hps, hu⟩ := hs
  refine ⟨σs.map (Env.mapVals w), ?_, unionAll_map w hu⟩
  clear hu
  induction hps with
  | nil => exact .nil
  | @cons p σ ps σs hp hps ih =>
      exact .cons (validSubst_map hd he hc h hw (hn p (by simp)) hp)
        (ih (fun p hp => hn p (List.mem_cons_of_mem _ hp)))

/-- A source match can be re-expressed using only recorded representatives of a
state with the same inferred facts. The returned relation supports head transport. -/
theorem validQuerySubst_transport {d e : Database} (hd : d.WF) (he : e.WF)
    (heStore : e.StoreOk)
    (hc : d.sig.AllConstructors) (h : d.SameMeaning e)
    {q : Query} {σ : Env} (hn : ∀ p ∈ q, p.OrderingFree)
    (hs : ValidQuerySubst d q σ) :
    ∃ τ, ValidQuerySubst e q τ ∧ EnvRelated e σ τ := by
  let w := representative e he
  have hw : ∀ t ∈ d.values, w t ∈ e.values ∧ e.Infers t (w t) := by
    intro t ht
    exact representative_spec he heStore (h.sig ▸ ht.2)
      ((h.inferred t t).mp (infers_of_held ht.1))
  exact ⟨Env.mapVals w σ, validQuerySubst_map hd he hc h hw hn hs,
    envRelated_map hs.mem_values (fun t ht => ⟨(hw t ht).1.2, (hw t ht).2⟩)⟩

/-- Ordering-free constructor queries observe only the inferred state. -/
theorem queryHolds_iff {d e : Database} (hd : d.WF) (he : e.WF)
    (hdStore : d.StoreOk) (heStore : e.StoreOk)
    (hc : d.sig.AllConstructors) (h : d.SameMeaning e)
    {q : Query} (hn : ∀ p ∈ q, p.OrderingFree) : QueryHolds d q ↔ QueryHolds e q := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ, _⟩ := validQuerySubst_transport hd he heStore hc h hn hσ
    exact ⟨τ, hτ⟩
  · rintro ⟨τ, hτ⟩
    have hc' : e.sig.AllConstructors := h.sig ▸ hc
    obtain ⟨σ, hσ, _⟩ := validQuerySubst_transport he hd hdStore hc' h.symm hn hτ
    exact ⟨σ, hσ⟩

private def withoutEnv (d : Database) : Database := {d with env := []}

private theorem withoutEnv_wf {d : Database} (hw : d.WF) : (withoutEnv d).WF :=
  hw.setEnv (by simp)

private theorem withoutEnv_same {d e : Database} (h : d.SameMeaning e) :
    (withoutEnv d).SameMeaning (withoutEnv e) := by
  refine ⟨h.sig, rfl, h.rules, fun a b => ?_⟩
  exact (infers_iff_of_eqs_eq (d := withoutEnv d) (e := d) rfl).trans
    ((h.inferred a b).trans (infers_iff_of_eqs_eq (d := e) (e := withoutEnv e) rfl))

private theorem evalAction_transport {d e d' : Database} (hd : d.WF) (he : e.WF)
    (hc : d.sig.AllConstructors)
    (h : (withoutEnv d).SameMeaning (withoutEnv e))
    (hσ : EnvRelated e d.env e.env) {a : Action} (hn : a.OrderingFree)
    (hs : evalAction d a = some d') :
    ∃ e', evalAction e a = some e' ∧
      (withoutEnv d').SameMeaning (withoutEnv e') := by
  have hsig : d.sig = e.sig := h.sig
  have hc' : e.sig.AllConstructors := hsig ▸ hc
  cases a with
  | expr exp =>
      simp only [evalAction, Expr.evalAtom_eq_eval hc] at hs
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨u, hu, htu⟩ := eval_congOn he hσ hn (hsig ▸ ht)
      refine ⟨e.addTerm u, ?_, ?_⟩
      · simp [evalAction, Expr.evalAtom_eq_eval hc', hu]
      · exact (h.addTerm (withoutEnv_wf hd) (withoutEnv_wf he) t).trans
          (sameMeaning_addTerm_congr (withoutEnv_wf he)
            (htu.mono ((show e.Contained (withoutEnv e) from ⟨subset_rfl⟩).addTerms_mono _)))
  | union a b =>
      obtain ⟨ta, hta, hs⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨tb, htb, hs⟩ := Option.bind_eq_some_iff.mp hs
      split at hs
      next => cases hs
      next hnl =>
        obtain rfl := Option.some.inj hs
        have hno : ta.isLit = false ∧ tb.isLit = false := by
          simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true] using hnl
        obtain ⟨ua, hua, hca⟩ := eval_congOn he hσ hn.1 (hsig ▸ hta)
        obtain ⟨ub, hub, hcb⟩ := eval_congOn he hσ hn.2 (hsig ▸ htb)
        have hnoa : ua.isLit = false := by
          cases hi : ua.isLit with
          | false => rfl
          | true =>
              have heq := hca.eq_of_isLit (he.addTerms [ta, ua]).litsIsolated (Or.inr hi)
              simp [heq, hi] at hno
        have hnob : ub.isLit = false := by
          cases hi : ub.isLit with
          | false => rfl
          | true =>
              have heq := hcb.eq_of_isLit (he.addTerms [tb, ub]).litsIsolated (Or.inr hi)
              simp [heq, hi] at hno
        have hlit : ta.isLit ∨ tb.isLit → ta = tb := by simp [hno.1, hno.2]
        have hlit' : ua.isLit ∨ ub.isLit → ua = ub := by simp [hnoa, hnob]
        refine ⟨e.addEq ua ub, ?_, ?_⟩
        · simp [evalAction, hua, hub, hnoa, hnob]
        · exact (h.addEq (withoutEnv_wf hd) (withoutEnv_wf he) ta tb hlit).trans
            (sameMeaning_addEq_congr (withoutEnv_wf he)
              (hca.mono ((show e.Contained (withoutEnv e) from ⟨subset_rfl⟩).addTerms_mono _))
              (hcb.mono ((show e.Contained (withoutEnv e) from ⟨subset_rfl⟩).addTerms_mono _))
              hlit hlit')

private theorem evalActions_transport {d e d' : Database} (hd : d.WF) (he : e.WF)
    (hc : d.sig.AllConstructors)
    (h : (withoutEnv d).SameMeaning (withoutEnv e))
    (hσ : EnvRelated e d.env e.env) {as : List Action} (hn : Actions.OrderingFree as)
    (hs : evalActions d as = some d') :
    ∃ e', evalActions e as = some e' ∧
      (withoutEnv d').SameMeaning (withoutEnv e') := by
  induction as generalizing d e with
  | nil =>
      obtain rfl := Option.some.inj hs
      exact ⟨e, rfl, h⟩
  | cons a as ih =>
      obtain ⟨mid, hm, hrest⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨mid', hm', hh⟩ := evalAction_transport hd he hc h hσ hn.1 hm
      have hrel : EnvRelated mid' mid.env mid'.env := by
        rw [evalAction_env hm, evalAction_env hm']
        exact hσ.mono (evalAction_contained hm') (evalAction_sig hm').symm
      have hctor : mid.sig.AllConstructors := by rw [evalAction_sig hm]; exact hc
      obtain ⟨e', he', hh'⟩ := ih (evalAction_wf hd hm) (evalAction_wf he hm')
        hctor hh hrel hn.2 hrest
      exact ⟨e', by simp [evalActions, hm', he'], hh'⟩

/-- A constructor rule head transports along inferred-state equivalence. Local
substitutions may use different recorded representatives; the surrounding program
environments are empty, as they are in executions from `Database.empty`. -/
theorem evalLocalActions_transport {d e d' : Database} (hd : d.WF) (he : e.WF)
    (hc : d.sig.AllConstructors) (h : d.SameMeaning e)
    (hdEnv : d.env = []) (heEnv : e.env = []) {σ τ : Env}
    (hs : ∀ b ∈ σ, b.2 ∈ d.terms) (ht : ∀ b ∈ τ, b.2 ∈ e.terms)
    (hσ : EnvRelated e σ τ) {as : List Action} (hn : Actions.OrderingFree as)
    (hr : evalLocalActions d as σ = some d') :
    ∃ e', evalLocalActions e as τ = some e' ∧ d'.SameMeaning e' := by
  obtain ⟨post, hpost, rfl⟩ := evalLocalActions_eq_some hr
  have hcore :
      (withoutEnv {d with env := σ ++ d.env}).SameMeaning
        (withoutEnv {e with env := τ ++ e.env}) := withoutEnv_same (d := d) (e := e) h
  have hrel : EnvRelated {e with env := τ ++ e.env}
      (σ ++ d.env) (τ ++ e.env) := by
    simpa only [hdEnv, heEnv, List.append_nil] using
      hσ.mono (show e.Contained {e with env := τ ++ e.env} from ⟨subset_rfl⟩) rfl
  obtain ⟨post', hpost', hh⟩ := evalActions_transport
    (hd.appendEnv hs) (he.appendEnv ht) hc hcore hrel hn hpost
  refine ⟨{post' with env := e.env, rules := e.rules}, ?_, ?_⟩
  · simp only [evalLocalActions, hpost', Option.map_some]
  · refine ⟨hh.sig, h.env, h.rules, fun a b => ?_⟩
    exact (infers_iff_of_eqs_eq
      (d := {post with env := d.env, rules := d.rules}) (e := withoutEnv post) rfl).trans
      ((hh.inferred a b).trans (infers_iff_of_eqs_eq
        (d := withoutEnv post') (e := {post' with env := e.env, rules := e.rules}) rfl))

end Egglog.SourceMeaning
