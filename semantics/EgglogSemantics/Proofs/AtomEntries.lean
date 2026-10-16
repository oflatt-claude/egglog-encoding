import EgglogSemantics.Spec.Database
import EgglogSemantics.Proofs.Term
import Mathlib.Data.Set.Finite.Lattice

/-! Derived rows obey ordinary insertion and deletion laws on valid atom facts. -/

namespace Egglog

namespace Term

theorem areValues_iff {sig : Signature} {ts : List Term} :
    areValues sig ts = true ↔ ∀ t ∈ ts, t.IsValue sig := by
  induction ts with
  | nil => simp [areValues]
  | cons t ts ih => simp [areValues, ih, IsValue]

@[simp] theorem isValue_app_iff {sig : Signature} {f : FnName} {ts : List Term} :
    (Term.app f ts).IsValue sig ↔ sig.IsCtor f ∧ ∀ t ∈ ts, t.IsValue sig := by
  simp only [IsValue, isValue, Bool.and_eq_true, decide_eq_true_eq, areValues_iff]

theorem IsValue.lit (sig : Signature) (l : Lit) : (Term.lit l).IsValue sig := rfl

theorem IsValue.app {sig : Signature} {f : FnName} {ts : List Term}
    (hf : sig.IsCtor f) (ht : ∀ t ∈ ts, t.IsValue sig) :
    (Term.app f ts).IsValue sig := isValue_app_iff.mpr ⟨hf, ht⟩

theorem IsValue.subterm {sig : Signature} {s t : Term}
    (ht : t.IsValue sig) (hs : s ∈ t.subterms) : s.IsValue sig := by
  induction hs with
  | refl => exact ht
  | arg ha _ ih => exact ih ((isValue_app_iff.mp ht).2 _ ha)

theorem IsValue.least {sig : Signature} {a b : Term}
    (ha : a.IsValue sig) (hb : b.IsValue sig) : (Term.least a b).IsValue sig := by
  unfold Term.least
  split <;> assumption

end Term

namespace Entry.Valid

theorem decl_spec {sig : Signature} {row : Entry} (h : row.Valid sig)
    {decl : FnDecl} (hd : sig row.name = some decl) :
    decl.merge ≠ none ∧ row.key.length = decl.arity ∧ row.value.length = decl.outArity := by
  obtain ⟨dc, hdc, hm, hk, ho, _⟩ := h
  obtain rfl := Option.some.inj (hdc.symm.trans hd)
  exact ⟨hm, hk, ho⟩

theorem column_values {sig : Signature} {row : Entry} (h : row.Valid sig) :
    ∀ t ∈ row.columns, t.IsValue sig := h.choose_spec.2.2.2.2

theorem key_values {sig : Signature} {row : Entry} (h : row.Valid sig) :
    ∀ t ∈ row.key, t.IsValue sig :=
  fun t ht => h.column_values t (List.mem_append_left _ ht)

theorem output_values {sig : Signature} {row : Entry} (h : row.Valid sig) :
    ∀ t ∈ row.value, t.IsValue sig :=
  fun t ht => h.column_values t (List.mem_append_right _ ht)

theorem with_value {sig : Signature} {row : Entry} {vs : List Term}
    (h : row.Valid sig) (hlen : vs.length = row.value.length)
    (hv : ∀ t ∈ vs, t.IsValue sig) :
    (Entry.mk row.name row.key vs).Valid sig := by
  obtain ⟨decl, hd, hm, hk, ho, hc⟩ := h
  refine ⟨decl, hd, hm, hk, hlen.trans ho, ?_⟩
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hc t (List.mem_append_left _ ht)
  · exact hv t ht

theorem atom_not_value {sig : Signature} {row : Entry} (h : row.Valid sig) :
    ¬ row.atom.IsValue sig := by
  obtain ⟨decl, hd, hm, _⟩ := h
  intro hv
  obtain ⟨ctor, hc, hnone⟩ := (Term.isValue_app_iff.mp hv).1
  obtain rfl := Option.some.inj (hc.symm.trans hd)
  exact hm hnone

theorem atom_injective {sig : Signature} {a b : Entry}
    (ha : a.Valid sig) (hb : b.Valid sig) (he : a.atom = b.atom) : a = b := by
  cases a with | mk f ks vs =>
    cases b with | mk g ls ws =>
      obtain ⟨rfl, hcols⟩ := Term.app.inj he
      obtain ⟨da, hda, _, hka, _⟩ := ha
      obtain ⟨db, hdb, _, hkb, _⟩ := hb
      obtain rfl := Option.some.inj (hda.symm.trans hdb)
      have hk : ks.length = ls.length := hka.trans hkb.symm
      obtain ⟨rfl, rfl⟩ := List.append_inj hcols hk
      rfl

theorem atom_subterm {sig : Signature} {a b : Entry}
    (ha : a.Valid sig) (hb : b.Valid sig) (hs : a.atom ∈ b.atom.subterms) : a = b := by
  rcases (Term.subterms_app (f := b.name) (args := b.columns)) ▸ hs with he | hs
  · exact ha.atom_injective hb he
  · obtain ⟨t, ht, hs⟩ := Set.mem_iUnion₂.mp hs
    exact (ha.atom_not_value ((hb.column_values t ht).subterm hs)).elim

end Entry.Valid

namespace Database

theorem mem_addTerm_entries {d : Database} {t : Term} {row : Entry} :
    row ∈ (d.addTerm t).entries ↔
      row ∈ d.entries ∨ (row.Valid d.sig ∧ row.atom = t) := by
  simp [entries, addTerm, and_or_left, or_comm]

theorem addTerm_entries {d : Database} {t : Term} (ht : t.IsValue d.sig) :
    (d.addTerm t).entries = d.entries := by
  ext row
  rw [mem_addTerm_entries]
  constructor
  · rintro (hr | ⟨hv, hs⟩)
    · exact hr
    · exact (hv.atom_not_value (hs.symm ▸ ht)).elim
  · exact Or.inl

theorem addTerms_entries {d : Database} {ts : List Term}
    (ht : ∀ t ∈ ts, t.IsValue d.sig) : (d.addTerms ts).entries = d.entries := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih =>
    change ((d.addTerm t).addTerms ts).entries = d.entries
    rw [ih (d := d.addTerm t) (fun s hs => ht s (List.mem_cons_of_mem _ hs)),
      addTerm_entries (ht t (by simp))]

theorem addEq_entries {d : Database} {a b : Term}
    (ha : a.IsValue d.sig) (_hb : b.IsValue d.sig) :
    (d.addEq a b).entries = d.entries := by
  ext row
  change (row.Valid d.sig ∧
    ((row.atom, row.atom) = (a, b) ∨ (row.atom, row.atom) ∈ _)) ↔ _
  constructor
  · rintro ⟨hv, he | he⟩
    · apply (hv.atom_not_value ?_).elim
      rw [show row.atom = a from congrArg Prod.fst he]
      exact ha
    · exact ⟨hv, he⟩
  · rintro ⟨hv, he⟩
    exact ⟨hv, Or.inr he⟩

theorem putEntry_entries {d : Database} {row : Entry} (hr : row.Valid d.sig) :
    (d.putEntry row).entries = insert row d.entries := by
  ext other
  rw [putEntry, mem_addTerm_entries]
  constructor
  · rintro (he | ⟨hv, hs⟩)
    · exact Or.inr he
    · exact Or.inl (hv.atom_injective hr hs)
  · rintro (rfl | he)
    · exact Or.inr ⟨hr, rfl⟩
    · exact Or.inl he

theorem eraseEntry_entries {d : Database} {row : Entry} (hr : row.Valid d.sig) :
    (d.eraseEntry row).entries = d.entries \ {row} := by
  ext other
  constructor
  · rintro ⟨hv, ⟨he, hne⟩ | ⟨t, ht, heq⟩⟩
    · refine ⟨⟨hv, he⟩, ?_⟩
      intro heq
      exact hne (congrArg (fun (e : Entry) => (e.atom, e.atom)) heq)
    · apply (hv.atom_not_value ?_).elim
      have hatom : other.atom = t := congrArg Prod.fst heq
      rw [hatom]
      exact hr.column_values t ht
  · rintro ⟨⟨hv, he⟩, hne⟩
    refine ⟨hv, Or.inl ⟨he, ?_⟩⟩
    intro heq
    exact hne (hv.atom_injective hr (congrArg Prod.fst heq))

theorem eraseEntry_entries_subset {d : Database} {row : Entry}
    (hr : row.Valid d.sig) : (d.eraseEntry row).entries ⊆ d.entries := by
  rw [eraseEntry_entries hr]
  exact Set.sdiff_subset

theorem finite_entries {d : Database} (he : d.eqs.Finite) : d.entries.Finite :=
  Set.Finite.of_injOn (f := fun row : Entry => (row.atom, row.atom))
    (fun _ h => h.2)
    (fun _ ha _ hb heq => ha.1.atom_injective hb.1 (congrArg Prod.fst heq)) he

theorem sUnion_entries {d : Database} {S : Set Database}
    (hs : ∀ e ∈ S, e.sig = d.sig) :
    (d.sUnion S).entries = d.entries ∪ ⋃ e ∈ S, e.entries := by
  ext row
  constructor
  · rintro ⟨hv, he | he⟩
    · exact Or.inl ⟨hv, he⟩
    · obtain ⟨e, hS, he⟩ := Set.mem_iUnion₂.mp he
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨e, hS, ⟨by simpa [sUnion, hs e hS] using hv, he⟩⟩)
  · rintro (⟨hv, he⟩ | he)
    · exact ⟨hv, Or.inl he⟩
    · obtain ⟨e, hS, hv, he⟩ := Set.mem_iUnion₂.mp he
      exact ⟨by simpa [sUnion, hs e hS] using hv, Or.inr (Set.mem_iUnion₂.mpr ⟨e, hS, he⟩)⟩

/-- Packing value equations and valid row diagonals recovers exactly those rows. -/
theorem entries_eq_of_packed {d : Database} {E : Set (Term × Term)} {rows : Set Entry}
    (he : d.eqs = E ∪ {(row.atom, row.atom) | row ∈ rows})
    (hv : ∀ p ∈ E, p.1.IsValue d.sig) (hr : ∀ row ∈ rows, row.Valid d.sig) :
    d.entries = rows := by
  ext row
  constructor
  · rintro ⟨hvalid, hmem⟩
    rw [he] at hmem
    rcases hmem with hmem | ⟨other, ho, heq⟩
    · exact (hvalid.atom_not_value (hv _ hmem)).elim
    · obtain rfl := (hr other ho).atom_injective hvalid (congrArg Prod.fst heq)
      exact ho
  · intro hrow
    refine ⟨hr row hrow, ?_⟩
    rw [he]
    exact Or.inr ⟨row, hrow, rfl⟩

end Database
end Egglog
