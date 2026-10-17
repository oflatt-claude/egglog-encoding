import EgglogSemantics.Proofs.Provenance.GeneratedWorld
import EgglogSemantics.Proofs.Provenance.GeneratedEvaluation
import EgglogSemantics.Proofs.Congruence.UFCoverage

namespace Egglog.Provenance.Generated

open Congruence Congruence.Abstract

private theorem row_mem_soundRows {src d : Database}
    (hshape : MergeShape d.sig) (hs : SoundTerms d src) {row : Entry}
    (hr : row ∈ d.entries) : row.atom ∈ SoundRows src := by
  obtain ⟨dc, hd, hm, hk, hv⟩ := hr.1
  obtain ⟨ms, hms⟩ := Option.ne_none_iff_exists'.mp hm
  cases ms with
  | merge oldVars newVars body res =>
      obtain ⟨hrole, _, _, hout, huf, _⟩ := hshape row.name dc hd body res hms
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hv.trans hout)
      have ht : Term.app row.name (row.key ++ [a]) ∈ d.terms := by
        simpa only [Entry.atom, Entry.columns, ha] using (StoredCong.direct hr.2).mem_left
      rcases hrole with hn | ⟨f, hn⟩
      · obtain ⟨key, he⟩ := List.length_eq_one_iff.mp (hk.trans (huf hn))
        refine Or.inr ⟨key, a, ?_, ?_⟩
        · simp only [Entry.atom, Entry.columns, hn, he, ha, List.cons_append,
            List.nil_append]
        · simpa only [hn, he, List.cons_append, List.nil_append] using hs.2 key a
            (by simpa only [hn, he, List.cons_append, List.nil_append] using ht)
      · refine Or.inl ⟨f, row.key, a, ?_, ?_⟩
        · simp only [Entry.atom, Entry.columns, hn, ha]
        · exact hs.1 f row.key a (hn ▸ ht)

/-- A genuine generated collision preserves the finite semantic witness world. -/
theorem World.mergeStep {P : Program} {src d e : Database}
    (h : World P src d) (hm : MergeStep d e) : World P src e := by
  have hshape : MergeShape d.sig := h.signature ▸ encodeSig_mergeShape P
  have hc : MergeClosure d e := .single hm
  have hr := h.runtime.merge hc
  have hs := mergeStep_soundTerms hshape h.runtime.noUnions.diag h.runtime.wf
    h.runtime.storeOk h.runtime.state.uf h.sound hm
  refine ⟨hr, hm.sig.trans h.signature, hm.envRules.1.trans h.environment,
    hm.envRules.2.trans h.rules, hs,
    mergeStep_descending hshape h.runtime.noUnions.diag h.runtime.wf h.runtime.storeOk
      h.runtime.state.uf h.descending hm, ?_⟩
  intro t ht
  rcases hr.storeOk.term ht with hv | ⟨row, hrow, he⟩
  · exact h.bound (Live.mergeStep_values_subset h.runtime hshape hm ⟨ht, hv⟩).1
  · subst t
    exact Or.inr (row_mem_soundRows (hm.sig ▸ hshape) hs
      (hr.storeOk.entry_of_held_atom hrow ht))

private theorem table_entry_valid {sig : Signature} {f : FnName} {k : Nat}
    {cols : List Term} (hd : sig f = some (tableDecl k))
    (hlen : cols.length = k + 1) (ha : SourceProof.atomOk sig (.app f cols) = true) :
    (Entry.mk f (cols.take k) (cols.drop k)).Valid sig := by
  simp only [SourceProof.atomOk, hd, Option.any_some, Bool.and_eq_true_iff] at ha
  refine ⟨tableDecl k, hd, by simp [tableDecl], ?_, ?_, ?_⟩
  · simp only [List.length_take, hlen, tableDecl]
    omega
  · simp only [List.length_drop, hlen, tableDecl]
    omega
  · simpa only [Entry.columns, List.take_append_drop] using
      SourceProof.valuesOk_isValue ha.2

/-- A successful generated merge certificate has two distinct rows, so it is realized
by an actual collision in a world containing both inputs. -/
theorem mergeFacts_step {d : Database} (h : Live.Runtime d)
    {f : FnName} {old new : Term} {fs : MergeFacts}
    (ho : old ∈ d.terms) (hn : new ∈ d.terms)
    (hao : SourceProof.atomOk d.sig old = true)
    (han : SourceProof.atomOk d.sig new = true)
    (hf : mergeFacts d.sig f old new = some fs) :
    ∃ post, MergeStep d post ∧
      ∀ t, t ∈ fs.body ∨ t ∈ fs.result.subtermList → t ∈ post.terms := by
  unfold mergeFacts at hf
  obtain ⟨dc, hd, hdecl⟩ := Option.bind_eq_some_iff.mp hf
  cases hm : dc.merge with
  | none => simp [hm] at hdecl
  | some ms =>
      obtain ⟨k, rfl⟩ := h.generated f dc hd (by simp [hm])
      obtain rfl : ms = .merge ["old"] ["new"] mergeBody mergeResult := by
        simpa [tableDecl, eq_comm] using hm
      simp only [tableDecl] at hdecl
      cases old with
      | lit _ => simp at hdecl
      | app ofn oc =>
        cases new with
        | lit _ => simp at hdecl
        | app nfn nc =>
          simp only at hdecl
          split at hdecl
          · rename_i hcols
            simp only [Bool.and_eq_true_iff, beq_iff_eq, bne_iff_ne] at hcols
            obtain ⟨⟨⟨⟨⟨hfo, hfn⟩, hoc⟩, hnc⟩, hkeys⟩, hne⟩ := hcols
            subst ofn
            subst nfn
            have hoc' : oc.length = k + 1 := by simpa [FnDecl.entryWidth] using hoc
            have hnc' : nc.length = k + 1 := by simpa [FnDecl.entryWidth] using hnc
            let oldRow : Entry := ⟨f, oc.take k, oc.drop k⟩
            let newRow : Entry := ⟨f, nc.take k, nc.drop k⟩
            have hro : oldRow ∈ d.entries :=
              h.storeOk.entry_of_held_atom (table_entry_valid hd hoc' hao) (by
                simpa [oldRow, Entry.atom, Entry.columns] using ho)
            have hrn : newRow ∈ d.entries :=
              h.storeOk.entry_of_held_atom (table_entry_valid hd hnc' han) (by
                simpa [newRow, Entry.atom, Entry.columns] using hn)
            have hrows : oldRow ≠ newRow := by
              intro he
              apply hne
              simpa [oldRow, newRow, Entry.atom, Entry.columns] using congrArg Entry.atom he
            obtain ⟨facts, hbody, hafterBody⟩ := Option.bind_eq_some_iff.mp hdecl
            obtain ⟨vs, hres, hafterRes⟩ := Option.bind_eq_some_iff.mp hafterBody
            split at hafterRes
            · cases Option.some.inj hafterRes
              let base := (d.eraseEntry oldRow).eraseEntry newRow
              let ρ := mergeEnv ["old"] ["new"] (oc.drop k) (nc.drop k)
              obtain ⟨D, hD, hfs⟩ := actionsFacts_sound (db := { base with env := ρ }) hbody
              have hv : Expr.evalList D.sig mergeResult D.env = some vs := by
                rw [evalActions_sig hD, evalActions_env hD]; exact hres
              have hmerge : evalMerge { base with env := ρ } mergeBody mergeResult = some (D, vs) := by
                simp [evalMerge, hD, hv]
              let post := ({ D with env := d.env, rules := d.rules } : Database).putEntry
                ⟨f, oc.take k, vs⟩
              have hk : CongList d oldRow.key newRow.key := by
                change CongList d (oc.take k) (nc.take k)
                rw [← hkeys]
                exact CongList.refl fun t ht => h.storeOk.columns oldRow hro t
                  (List.mem_append_left _ ht)
              have hstep : MergeStep d post := .collide' hro hrn hrows rfl hd hk
                (.eval rfl hmerge)
              refine ⟨post, hstep, ?_⟩
              intro t ht
              rcases ht with ht | ht
              · have hkeep : D.Contained { D with env := d.env, rules := d.rules } :=
                  ⟨fun _ hp => hp⟩
                exact (Database.Contained.putEntry _ _).terms (hkeep.terms (hfs t ht))
              · exact post.subtermClosed _ (Database.mem_addTerm _ _)
                  ((Term.mem_subtermList _).mp ht)
            · contradiction
          · contradiction

theorem mergeFacts_closed {P : Program} {src : Database} (hp : P.Fragment)
    {f : FnName} {old new : Term} {fs : MergeFacts}
    (ho : Fact P src old) (hn : Fact P src new)
    (hao : SourceProof.atomOk (encodeSig P) old = true)
    (han : SourceProof.atomOk (encodeSig P) new = true)
    (hf : mergeFacts (encodeSig P) f old new = some fs) :
    ∀ t, t ∈ fs.body ∨ t ∈ fs.result.subtermList → Fact P src t := by
  obtain ⟨d, hd, hh⟩ := Fact.collect (src := src) hp (ts := [old, new]) (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    exacts [ho, hn])
  obtain ⟨post, hm, hpost⟩ := mergeFacts_step hd.runtime
    (hh old (by simp)) (hh new (by simp))
    (hd.signature ▸ hao) (hd.signature ▸ han) (hd.signature ▸ hf)
  exact fun t ht => ⟨post, hd.mergeStep hm, hpost t ht⟩

end Egglog.Provenance.Generated
