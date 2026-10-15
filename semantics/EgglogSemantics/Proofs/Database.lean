import EgglogSemantics.Spec.Congruence
import EgglogSemantics.Proofs.Term

namespace Egglog
namespace Env
@[simp] theorem lookup_nil {v : Var} : lookup v [] = none := rfl

@[simp] theorem lookup_cons {v w : Var} {t : Term} {σ : Env} :
    lookup v ((w, t) :: σ) = if v = w then some t else lookup v σ := rfl

@[simp] theorem dom_nil : dom [] = [] := rfl

@[simp] theorem dom_cons {v : Var} {t : Term} {σ : Env} :
    dom ((v, t) :: σ) = v :: dom σ := rfl

theorem mem_dom_of_mem {b : Var × Term} {σ : Env} (h : b ∈ σ) : b.1 ∈ dom σ :=
  List.mem_map_of_mem h

theorem mem_dom_iff {v : Var} {σ : Env} : v ∈ dom σ ↔ ∃ t, (v, t) ∈ σ := by
  constructor
  · intro h
    obtain ⟨⟨w, t⟩, hb, rfl⟩ := List.mem_map.mp h
    exact ⟨t, hb⟩
  · rintro ⟨t, hb⟩
    exact mem_dom_of_mem hb

@[simp] theorem dom_append {σ₁ σ₂ : Env} : dom (σ₁ ++ σ₂) = dom σ₁ ++ dom σ₂ :=
  List.map_append ..

theorem lookup_isSome_iff_mem_dom {v : Var} {σ : Env} :
    (lookup v σ).isSome ↔ v ∈ dom σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases h : v = w <;> simp [h, ih]

theorem lookup_eq_none_iff {v : Var} {σ : Env} : lookup v σ = none ↔ v ∉ dom σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases h : v = w <;> simp [h, ih]

/-- Appending environments never fails, unlike `Env.Union2`, because the only appends
this semantics performs are of a substitution onto the globals, whose domains are
disjoint (`Pattern.freeVars_lookup_eq_none`). `lookup` is left-biased, so `σ₁` shadows
`σ₂` — the same bias `Env.Union2` has. -/
theorem lookup_append_of_not_mem {v : Var} {σ₁ σ₂ : Env} (h : v ∉ dom σ₁) :
    lookup v (σ₁ ++ σ₂) = lookup v σ₂ := by
  induction σ₁ with
  | nil => rfl
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    simp only [dom_cons, List.mem_cons, not_or] at h
    simp [h.1, ih h.2]

theorem lookup_append_of_mem {v : Var} {σ₁ σ₂ : Env} (h : v ∈ dom σ₁) :
    lookup v (σ₁ ++ σ₂) = lookup v σ₁ := by
  induction σ₁ with
  | nil => simp at h
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases hv : v = w
    · simp [hv]
    · simp only [dom_cons, List.mem_cons] at h
      simp [hv, ih (h.resolve_left hv)]

theorem mem_of_lookup {v : Var} {t : Term} {σ : Env} (h : lookup v σ = some t) :
    (v, t) ∈ σ := by
  induction σ with
  | nil => simp at h
  | cons b σ ih =>
    obtain ⟨w, u⟩ := b
    by_cases hv : v = w
    · subst hv
      rw [lookup_cons, if_pos rfl] at h
      cases h
      simp
    · rw [lookup_cons, if_neg hv] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- With no duplicate variables, `lookup` is just membership. -/
theorem lookup_eq_some_iff_mem {v : Var} {t : Term} {σ : Env} (hnd : (dom σ).Nodup) :
    lookup v σ = some t ↔ (v, t) ∈ σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, u⟩ := b
    rw [dom_cons, List.nodup_cons] at hnd
    by_cases hv : v = w
    · subst hv
      simp only [lookup_cons, ↓reduceIte, Option.some.injEq, List.mem_cons, Prod.mk.injEq,
        true_and]
      exact ⟨fun h => Or.inl h.symm,
        fun h => h.elim Eq.symm fun hmem => absurd (mem_dom_of_mem hmem) hnd.1⟩
    · simp only [lookup_cons, hv, ↓reduceIte, List.mem_cons, Prod.mk.injEq, ih hnd.2,
        false_and, false_or]

theorem Agree.refl (σ : Env) : Agree σ σ := fun _ => rfl

theorem Agree.symm {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) : Agree σ₂ σ₁ := fun v => (h v).symm

theorem Agree.trans {σ₁ σ₂ σ₃ : Env} (h₁ : Agree σ₁ σ₂) (h₂ : Agree σ₂ σ₃) :
    Agree σ₁ σ₃ := fun v => (h₁ v).trans (h₂ v)

/-- Reordering a duplicate-free environment's bindings changes no lookup. This is
what makes `ValidEnv`'s use of `Perm`, rather than fixing the order of `σ`'s bindings,
observationally harmless. -/
theorem Agree.of_perm {σ₁ σ₂ : Env} (h : σ₁.Perm σ₂) (hnd : (dom σ₁).Nodup) :
    Agree σ₁ σ₂ := by
  have hp : (dom σ₁).Perm (dom σ₂) := h.map Prod.fst
  intro v
  cases hl : lookup v σ₁ with
  | some t =>
    exact ((lookup_eq_some_iff_mem (hp.nodup hnd)).mpr
      (h.mem_iff.mp ((lookup_eq_some_iff_mem hnd).mp hl))).symm
  | none =>
    rw [lookup_eq_none_iff] at hl
    exact (lookup_eq_none_iff.mpr fun hv => hl (hp.mem_iff.mpr hv)).symm

/-- Agreement survives a shared prefix, which is how a substitution's agreement
lifts to the globals it is appended to. -/
theorem Agree.append_left (ρ : Env) {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) :
    Agree (ρ ++ σ₁) (ρ ++ σ₂) := by
  intro v
  by_cases hv : v ∈ dom ρ
  · rw [lookup_append_of_mem hv, lookup_append_of_mem hv]
  · rw [lookup_append_of_not_mem hv, lookup_append_of_not_mem hv]
    exact h v

/-- Agreement survives a shared **suffix**, which is the order a rule firing appends in: the
substitution first, the globals behind it (`evalLocalActions`). -/
theorem Agree.append_right (ρ : Env) {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) :
    Agree (σ₁ ++ ρ) (σ₂ ++ ρ) := by
  intro v
  by_cases hv : v ∈ dom σ₁
  · have hv₂ : v ∈ dom σ₂ := by
      rw [← lookup_isSome_iff_mem_dom, ← h v, lookup_isSome_iff_mem_dom]; exact hv
    rw [lookup_append_of_mem hv, lookup_append_of_mem hv₂]; exact h v
  · have hv₂ : v ∉ dom σ₂ := by
      rw [← lookup_eq_none_iff, ← h v, lookup_eq_none_iff]; exact hv
    rw [lookup_append_of_not_mem hv, lookup_append_of_not_mem hv₂]

end Env
/-! ### What the database holds

`Database.terms` is a `def` over `Cong`, not a field, so the lemmas below are proved rather
than `rfl`. They all come from one fact: no rule of `Cong` introduces a term the equations
do not already name, so `terms` is a comprehension over `eqs`. -/

/-- **A derivation mentions only what the equations name.** Both endpoints of a `Cong` are
endpoints of an asserted equation; with no reflexivity rule there is nowhere else for a
term to come from. -/
theorem Cong.mem_endpoints {db : Database} {a b : Term} (h : Cong db a b) :
    (∃ u, (a, u) ∈ db.eqs ∨ (u, a) ∈ db.eqs) ∧
      (∃ u, (b, u) ∈ db.eqs ∨ (u, b) ∈ db.eqs) := by
  induction h using Cong.rec (motive_2 := fun _ _ _ => True) with
  | assert hab => exact ⟨⟨_, Or.inl hab⟩, ⟨_, Or.inr hab⟩⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | congr _ _ _ ih₁ ih₂ _ => exact ⟨ih₁.1, ih₂.1⟩
  | nil => trivial
  | cons => trivial

namespace Database
/-- **The terms are exactly the endpoints of the asserted equations.** Every `terms` lemma
below is this plus set algebra. -/
theorem mem_terms_iff {db : Database} {t : Term} :
    t ∈ db.terms ↔ ∃ u, (t, u) ∈ db.eqs ∨ (u, t) ∈ db.eqs :=
  ⟨fun ht => (Cong.mem_endpoints ht).1, fun ⟨_, h⟩ =>
    h.elim (fun h => (eqsInTerms_free (Cong.assert h)).1)
      fun h => (eqsInTerms_free (Cong.assert h)).2⟩

/-- Two databases asserting the same equations hold the same values. -/
theorem terms_eq_of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) :
    d₁.terms = d₂.terms := by
  ext t
  simp only [mem_terms_iff, h]

@[simp] theorem empty_terms : Database.empty.terms = ∅ := by
  ext t; simp [mem_terms_iff, Database.empty]

@[simp] theorem addTerm_terms {t : Term} {db : Database} :
    (db.addTerm t).terms = db.terms ∪ t.subterms := by
  ext s
  simp only [mem_terms_iff, Database.addTerm, Set.mem_union, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨u, (h | ⟨v, hv, hv₁, hv₂⟩) | (h | ⟨v, hv, hv₁, hv₂⟩)⟩
    · exact Or.inl ⟨u, Or.inl h⟩
    · exact Or.inr (hv₁ ▸ hv)
    · exact Or.inl ⟨u, Or.inr h⟩
    · exact Or.inr (hv₂ ▸ hv)
  · rintro (⟨u, h | h⟩ | h)
    · exact ⟨u, Or.inl (Or.inl h)⟩
    · exact ⟨u, Or.inr (Or.inl h)⟩
    · exact ⟨s, Or.inl (Or.inr ⟨s, h, rfl, rfl⟩)⟩

@[simp] theorem addTerm_eqs {t : Term} {db : Database} :
    (db.addTerm t).eqs = db.eqs ∪ {(s, s) | s ∈ t.subterms} := rfl

@[simp] theorem addTerm_sig {t : Term} {db : Database} : (db.addTerm t).sig = db.sig := rfl

@[simp] theorem addTerm_env {t : Term} {db : Database} : (db.addTerm t).env = db.env := rfl

@[simp] theorem addTerm_rules {t : Term} {db : Database} :
    (db.addTerm t).rules = db.rules := rfl

@[simp] theorem addTerm_entries {t : Term} {db : Database} :
    (db.addTerm t).entries = db.entries := rfl

@[simp] theorem addTerm_pending {t : Term} {db : Database} :
    (db.addTerm t).pending = db.pending := rfl

theorem mem_addTerm (t : Term) (db : Database) : t ∈ (db.addTerm t).terms :=
  Cong.assert (Or.inr ⟨t, Term.IsSubterm.refl t, rfl⟩)

@[simp] theorem addEq_eqs {a b : Term} {db : Database} :
    (db.addEq a b).eqs = insert (a, b) ((db.addTerm a).addTerm b).eqs := rfl

/-- Asserting an equation between terms the database already holds adds no terms. -/
theorem terms_insert_eq {db : Database} {a b : Term} (ha : a ∈ db.terms) (hb : b ∈ db.terms) :
    ({ db with eqs := insert (a, b) db.eqs } : Database).terms = db.terms := by
  obtain ⟨ua, ha⟩ := mem_terms_iff.mp ha
  obtain ⟨ub, hb⟩ := mem_terms_iff.mp hb
  ext s
  simp only [mem_terms_iff, Set.mem_insert_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨u, (⟨rfl, rfl⟩ | h) | (⟨rfl, rfl⟩ | h)⟩
    · exact ⟨ua, ha⟩
    · exact ⟨u, Or.inl h⟩
    · exact ⟨ub, hb⟩
    · exact ⟨u, Or.inr h⟩
  · rintro ⟨u, h⟩
    exact ⟨u, h.imp Or.inr Or.inr⟩

@[simp] theorem addEq_terms {a b : Term} {db : Database} :
    (db.addEq a b).terms = db.terms ∪ a.subterms ∪ b.subterms := by
  have ha : a ∈ ((db.addTerm a).addTerm b).terms := by
    simp only [addTerm_terms]; exact Or.inl (Or.inr a.self_mem_subterms)
  have hb : b ∈ ((db.addTerm a).addTerm b).terms := by
    simp only [addTerm_terms]; exact Or.inr b.self_mem_subterms
  change ({ (db.addTerm a).addTerm b with
      eqs := insert (a, b) ((db.addTerm a).addTerm b).eqs } : Database).terms = _
  rw [terms_insert_eq ha hb, addTerm_terms, addTerm_terms]

@[simp] theorem addEq_env {a b : Term} {db : Database} : (db.addEq a b).env = db.env := rfl

@[simp] theorem addEq_rules {a b : Term} {db : Database} :
    (db.addEq a b).rules = db.rules := rfl

@[simp] theorem addEq_sig {a b : Term} {db : Database} : (db.addEq a b).sig = db.sig := rfl

@[simp] theorem addEq_entries {a b : Term} {db : Database} :
    (db.addEq a b).entries = db.entries := rfl

@[simp] theorem addEq_pending {a b : Term} {db : Database} :
    (db.addEq a b).pending = db.pending := rfl

@[simp] theorem sUnion_entries {db : Database} {S : Set Database} :
    (db.sUnion S).entries = db.entries ∪ ⋃ d ∈ S, d.entries := rfl

@[simp] theorem sUnion_pending {db : Database} {S : Set Database} :
    (db.sUnion S).pending = db.pending ∪ ⋃ d ∈ S, d.pending := rfl

@[simp] theorem sUnion_eqs {db : Database} {S : Set Database} :
    (db.sUnion S).eqs = db.eqs ∪ ⋃ d ∈ S, d.eqs := rfl

@[simp] theorem sUnion_terms {db : Database} {S : Set Database} :
    (db.sUnion S).terms = db.terms ∪ ⋃ d ∈ S, d.terms := by
  ext s
  simp only [Set.mem_union, Set.mem_iUnion, mem_terms_iff, sUnion_eqs, exists_prop]
  constructor
  · rintro ⟨u, (h | ⟨d, hd, h⟩) | (h | ⟨d, hd, h⟩)⟩
    · exact Or.inl ⟨u, Or.inl h⟩
    · exact Or.inr ⟨d, hd, u, Or.inl h⟩
    · exact Or.inl ⟨u, Or.inr h⟩
    · exact Or.inr ⟨d, hd, u, Or.inr h⟩
  · rintro (⟨u, h⟩ | ⟨d, hd, u, h⟩)
    · exact ⟨u, h.imp Or.inl Or.inl⟩
    · exact ⟨u, h.imp (fun h => Or.inr ⟨d, hd, h⟩) fun h => Or.inr ⟨d, hd, h⟩⟩

@[simp] theorem sUnion_env {db : Database} {S : Set Database} :
    (db.sUnion S).env = db.env := rfl

@[simp] theorem sUnion_rules {db : Database} {S : Set Database} :
    (db.sUnion S).rules = db.rules := rfl

@[simp] theorem sUnion_sig {db : Database} {S : Set Database} :
    (db.sUnion S).sig = db.sig := rfl

/-- Two `EnvAgree` databases with the same environment and rules imposed are equal.
This is what turns agreement back into equality once `evalLocalActions` restores the
caller's environment. -/
theorem EnvAgree.eq_of_env_rules {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (σ : Env)
    (R : Set Rule) :
    ({ d₁ with env := σ, rules := R } : Database) = { d₂ with env := σ, rules := R } := by
  rw [h.sig, h.eqs, h.entries, h.pending]

/-! ### `addTerms`

`addTerms` is a fold, so its untouched fields need an induction rather than `rfl`. -/

/-- One extension by a concatenation is two extensions in a row: the fold law that lets an
appended operand list be worked with as the nested `(db.addTerms ts).addTerms us` every
other `addTerms` lemma is stated at. -/
theorem addTerms_append {db : Database} {ts us : List Term} :
    db.addTerms (ts ++ us) = (db.addTerms ts).addTerms us :=
  List.foldl_append ..

@[simp] theorem addTerms_sig {db : Database} {ts : List Term} :
    (db.addTerms ts).sig = db.sig := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addTerms_env {db : Database} {ts : List Term} :
    (db.addTerms ts).env = db.env := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addTerms_rules {db : Database} {ts : List Term} :
    (db.addTerms ts).rules = db.rules := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addTerms_entries {db : Database} {ts : List Term} :
    (db.addTerms ts).entries = db.entries := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addTerms_pending {db : Database} {ts : List Term} :
    (db.addTerms ts).pending = db.pending := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addTerms_terms {db : Database} {ts : List Term} :
    (db.addTerms ts).terms = db.terms ∪ {s | ∃ t ∈ ts, s ∈ t.subterms} := by
  induction ts generalizing db with
  | nil => change db.terms = _; simp
  | cons t ts ih =>
    change ((db.addTerm t).addTerms ts).terms = _
    rw [ih, addTerm_terms]
    ext s
    simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons]
    constructor
    · rintro ((hs | hs) | ⟨u, hu, hs⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨t, Or.inl rfl, hs⟩
      · exact Or.inr ⟨u, Or.inr hu, hs⟩
    · rintro (hs | ⟨u, rfl | hu, hs⟩)
      · exact Or.inl (Or.inl hs)
      · exact Or.inl (Or.inr hs)
      · exact Or.inr ⟨u, hu, hs⟩

theorem mem_addTerms {db : Database} {ts : List Term} {t : Term} (h : t ∈ ts) :
    t ∈ (db.addTerms ts).terms :=
  addTerms_terms ▸ Or.inr ⟨t, h, t.self_mem_subterms⟩

theorem addTerms_setRules (db : Database) (R : Set Rule) (ts : List Term) :
    ({ db with rules := R } : Database).addTerms ts = { db.addTerms ts with rules := R } := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih (db.addTerm t)

theorem addTerms_setSig (db : Database) (sig : Signature) (ts : List Term) :
    ({ db with sig := sig } : Database).addTerms ts = { db.addTerms ts with sig := sig } := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih (db.addTerm t)

/-! ### Current entries and pending writes -/

@[simp] theorem writeEntry_eqs {db : Database} {e : Entry} :
    (db.writeEntry e).eqs = (db.addTerms e.columns).eqs := rfl
@[simp] theorem writeEntry_sig {db : Database} {e : Entry} :
    (db.writeEntry e).sig = db.sig := addTerms_sig
@[simp] theorem writeEntry_env {db : Database} {e : Entry} :
    (db.writeEntry e).env = db.env := addTerms_env
@[simp] theorem writeEntry_rules {db : Database} {e : Entry} :
    (db.writeEntry e).rules = db.rules := addTerms_rules
@[simp] theorem writeEntry_entries {db : Database} {e : Entry} :
    (db.writeEntry e).entries = db.entries := addTerms_entries
@[simp] theorem writeEntry_pending {db : Database} {e : Entry} :
    (db.writeEntry e).pending = insert e db.pending := by simp [writeEntry]
@[simp] theorem writeEntry_terms {db : Database} {e : Entry} :
    (db.writeEntry e).terms = (db.addTerms e.columns).terms := terms_eq_of_eqs_eq rfl

@[simp] theorem putEntry_eqs {db : Database} {e : Entry} :
    (db.putEntry e).eqs = (db.addTerms e.columns).eqs := rfl
@[simp] theorem putEntry_sig {db : Database} {e : Entry} :
    (db.putEntry e).sig = db.sig := addTerms_sig
@[simp] theorem putEntry_env {db : Database} {e : Entry} :
    (db.putEntry e).env = db.env := addTerms_env
@[simp] theorem putEntry_rules {db : Database} {e : Entry} :
    (db.putEntry e).rules = db.rules := addTerms_rules
@[simp] theorem putEntry_entries {db : Database} {e : Entry} :
    (db.putEntry e).entries = insert e db.entries := by simp [putEntry]
@[simp] theorem putEntry_pending {db : Database} {e : Entry} :
    (db.putEntry e).pending = db.pending := addTerms_pending
@[simp] theorem putEntry_terms {db : Database} {e : Entry} :
    (db.putEntry e).terms = (db.addTerms e.columns).terms := terms_eq_of_eqs_eq rfl

@[simp] theorem consumeWrite_sig {db : Database} {e : Entry} :
    (db.consumeWrite e).sig = db.sig := rfl
@[simp] theorem consumeWrite_env {db : Database} {e : Entry} :
    (db.consumeWrite e).env = db.env := rfl
@[simp] theorem consumeWrite_rules {db : Database} {e : Entry} :
    (db.consumeWrite e).rules = db.rules := rfl
@[simp] theorem consumeWrite_eqs {db : Database} {e : Entry} :
    (db.consumeWrite e).eqs = db.eqs := rfl
@[simp] theorem eraseEntry_sig {db : Database} {e : Entry} :
    (db.eraseEntry e).sig = db.sig := rfl
@[simp] theorem eraseEntry_env {db : Database} {e : Entry} :
    (db.eraseEntry e).env = db.env := rfl
@[simp] theorem eraseEntry_rules {db : Database} {e : Entry} :
    (db.eraseEntry e).rules = db.rules := rfl
@[simp] theorem eraseEntry_eqs {db : Database} {e : Entry} :
    (db.eraseEntry e).eqs = db.eqs := rfl

@[simp] theorem putEntry_setRules (db : Database) (R : Set Rule) (e : Entry) :
    ({ db with rules := R } : Database).putEntry e = { db.putEntry e with rules := R } := by
  simp [putEntry, addTerms_setRules]

@[simp] theorem writeEntry_setRules (db : Database) (R : Set Rule) (e : Entry) :
    ({ db with rules := R } : Database).writeEntry e = { db.writeEntry e with rules := R } := by
  simp [writeEntry, addTerms_setRules]

@[simp] theorem putEntry_setSig (db : Database) (sig : Signature) (e : Entry) :
    ({ db with sig := sig } : Database).putEntry e = { db.putEntry e with sig := sig } := by
  simp [putEntry, addTerms_setSig]

@[simp] theorem writeEntry_setSig (db : Database) (sig : Signature) (e : Entry) :
    ({ db with sig := sig } : Database).writeEntry e = { db.writeEntry e with sig := sig } := by
  simp [writeEntry, addTerms_setSig]

theorem mem_writeEntry_columns {db : Database} {e : Entry} {t : Term}
    (ht : t ∈ e.columns) : t ∈ (db.writeEntry e).terms := by
  rw [writeEntry_terms]
  exact mem_addTerms ht

theorem mem_putEntry_columns {db : Database} {e : Entry} {t : Term}
    (ht : t ∈ e.columns) : t ∈ (db.putEntry e).terms := by
  rw [putEntry_terms]
  exact mem_addTerms ht

@[simp] theorem consumeWrite_terms {db : Database} {e : Entry} :
    (db.consumeWrite e).terms = db.terms := terms_eq_of_eqs_eq rfl
@[simp] theorem eraseEntry_terms {db : Database} {e : Entry} :
    (db.eraseEntry e).terms = db.terms := terms_eq_of_eqs_eq rfl

namespace EnvAgree
theorem addTerm {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (t : Term) :
    (d₁.addTerm t).EnvAgree (d₂.addTerm t) :=
  ⟨h.sig, by simp only [addTerm_eqs, h.eqs], h.entries, h.pending, h.rules, h.env⟩

theorem addTerms {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (ts : List Term) :
    (d₁.addTerms ts).EnvAgree (d₂.addTerms ts) := by
  induction ts generalizing d₁ d₂ with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem writeEntry {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (e : Entry) :
    (d₁.writeEntry e).EnvAgree (d₂.writeEntry e) := by
  have ht := h.addTerms e.columns
  exact ⟨ht.sig, ht.eqs, ht.entries, congrArg (insert e) ht.pending, ht.rules, ht.env⟩

theorem putEntry {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (e : Entry) :
    (d₁.putEntry e).EnvAgree (d₂.putEntry e) := by
  have ht := h.addTerms e.columns
  exact ⟨ht.sig, ht.eqs, congrArg (insert e) ht.entries, ht.pending, ht.rules, ht.env⟩

end EnvAgree
namespace Contained
theorem refl (db : Database) : Contained db db := ⟨subset_rfl⟩

theorem trans {d₁ d₂ d₃ : Database} (h₁ : Contained d₁ d₂) (h₂ : Contained d₂ d₃) :
    Contained d₁ d₃ := ⟨h₁.eqs.trans h₂.eqs⟩

theorem addTerm (t : Term) (db : Database) : Contained db (db.addTerm t) :=
  ⟨Set.subset_union_left⟩

theorem addTerms (ts : List Term) (db : Database) : Contained db (db.addTerms ts) := by
  induction ts generalizing db with
  | nil => exact refl db
  | cons t ts ih => exact (addTerm t db).trans (ih (db := db.addTerm t))

theorem addEq (a b : Term) (db : Database) : Contained db (db.addEq a b) :=
  ((addTerm a db).trans (addTerm b _)).trans ⟨Set.subset_insert _ _⟩

/-! The same operation applied to both sides. This is what makes an action, and hence a
whole action block, transportable along `Contained`. -/
/-- `Contained` is preserved by adding the same term to both sides. -/
theorem addTerm_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (t : Term) :
    (d₁.addTerm t).Contained (d₂.addTerm t) :=
  ⟨Set.union_subset_union h.eqs subset_rfl⟩

/-- `addTerm_mono` folded. -/
theorem addTerms_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (ts : List Term) :
    (d₁.addTerms ts).Contained (d₂.addTerms ts) := by
  induction ts generalizing d₁ d₂ with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm_mono t)

/-- The same equality is inserted on both sides, so `Set.insert_subset_insert` closes the
`eqs` component. -/
theorem addEq_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (a b : Term) :
    (d₁.addEq a b).Contained (d₂.addEq a b) :=
  ⟨Set.insert_subset_insert ((h.addTerm_mono a).addTerm_mono b).eqs⟩

theorem writeEntry (e : Entry) (db : Database) : Contained db (db.writeEntry e) :=
  ⟨(addTerms e.columns db).eqs⟩

theorem putEntry (e : Entry) (db : Database) : Contained db (db.putEntry e) :=
  ⟨(addTerms e.columns db).eqs⟩

theorem consumeWrite (e : Entry) (db : Database) : Contained db (db.consumeWrite e) :=
  ⟨subset_rfl⟩

theorem eraseEntry (e : Entry) (db : Database) : Contained db (db.eraseEntry e) :=
  ⟨subset_rfl⟩

theorem writeEntry_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (e : Entry) :
    (d₁.writeEntry e).Contained (d₂.writeEntry e) := ⟨(h.addTerms_mono e.columns).eqs⟩

theorem putEntry_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (e : Entry) :
    (d₁.putEntry e).Contained (d₂.putEntry e) := ⟨(h.addTerms_mono e.columns).eqs⟩

theorem sUnion (db : Database) (S : Set Database) : Contained db (db.sUnion S) :=
  ⟨Set.subset_union_left⟩

theorem mem_sUnion {db d : Database} {S : Set Database} (h : d ∈ S) :
    Contained d (db.sUnion S) :=
  ⟨fun _ ht => Or.inr (Set.mem_biUnion h ht)⟩

end Contained
namespace WF
theorem empty : WF Database.empty where
  eqsRefl := by simp
  subtermClosed := by simp
  envInTerms := by simp [Database.empty]
  litsIsolated := by simp [Database.empty, LitsIsolated]

theorem addTerm {db : Database} (h : WF db) (t : Term) : WF (db.addTerm t) where
  eqsRefl := by
    simp only [addTerm_terms, addTerm_eqs]
    rintro s (hs | hs)
    · exact Or.inl (h.eqsRefl s hs)
    · exact Or.inr ⟨s, hs, rfl⟩
  subtermClosed := by
    simp only [addTerm_terms]
    rintro s (hs | hs) u hu
    · exact Or.inl (h.subtermClosed s hs hu)
    · exact Or.inr (Term.subterms_subset_of_mem hs hu)
  envInTerms b hb := by
    simp only [addTerm_terms]; exact Or.inl (h.envInTerms b hb)
  litsIsolated := by
    rintro p (hp | ⟨s, -, rfl⟩)
    exacts [h.litsIsolated p hp, fun _ => rfl]

theorem addTerms {db : Database} (h : WF db) (ts : List Term) : WF (db.addTerms ts) := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

/-- `hlit` is what `evalAction`'s `union` check pays for: an equation with a literal
endpoint is reflexive, and `Database.LitsIsolated` survives. -/
theorem addEq {db : Database} (h : WF db) (a b : Term)
    (hlit : a.isLit ∨ b.isLit → a = b) : WF (db.addEq a b) where
  eqsRefl s hs := Set.mem_insert_of_mem _ (((h.addTerm a).addTerm b).eqsRefl s (by
    simpa only [addTerm_terms, ← Set.union_assoc] using
      (by simpa only [addEq_terms, ← Set.union_assoc] using hs)))
  subtermClosed := by
    simp only [addEq_terms]
    rintro s ((hs | hs) | hs) u hu
    · exact Or.inl (Or.inl (h.subtermClosed s hs hu))
    · exact Or.inl (Or.inr (Term.subterms_subset_of_mem hs hu))
    · exact Or.inr (Term.subterms_subset_of_mem hs hu)
  envInTerms b hb := by
    simp only [addEq_terms]; exact Or.inl (Or.inl (h.envInTerms b hb))
  litsIsolated := by
    rintro p (rfl | hp)
    · exact hlit
    · exact ((h.addTerm a).addTerm b).litsIsolated p hp

theorem sUnion {db : Database} (h : WF db) {S : Set Database}
    (hS : ∀ d ∈ S, WF d) : WF (db.sUnion S) where
  eqsRefl := by
    simp only [sUnion_terms, sUnion_eqs]
    rintro t (ht | ht)
    · exact Or.inl (h.eqsRefl t ht)
    · obtain ⟨d, hd, ht⟩ := Set.mem_iUnion₂.mp ht
      exact Or.inr (Set.mem_biUnion hd ((hS d hd).eqsRefl t ht))
  subtermClosed := by
    simp only [sUnion_terms]
    rintro t (ht | ht)
    · exact (h.subtermClosed t ht).trans Set.subset_union_left
    · obtain ⟨d, hd, ht⟩ := Set.mem_iUnion₂.mp ht
      exact ((hS d hd).subtermClosed t ht).trans
        (Set.subset_union_of_subset_right (Set.subset_biUnion_of_mem hd) _)
  envInTerms b hb := by
    simp only [sUnion_terms]; exact Or.inl (h.envInTerms b hb)
  litsIsolated := by
    rintro p (hp | hp)
    · exact h.litsIsolated p hp
    · obtain ⟨d, hd, hp⟩ := Set.mem_iUnion₂.mp hp
      exact (hS d hd).litsIsolated p hp

end WF
end Database
end Egglog
