import EgglogSemantics.Proofs.Provenance.GeneratedSoundness

namespace Egglog.Tests.GeneratedProvenance

open Congruence Provenance

def a : Term := .app "A" []
def b : Term := .app "B" []
def c : Term := .app "C" []
def seed : Rule :=
  ⟨[], [.union (.app "B" []) (.app "C" []),
    .union (.app "A" []) (.app "B" [])], "seed"⟩
def program : Program :=
  [.decl "A" (ctorDecl 0), .decl "B" (ctorDecl 0), .decl "C" (ctorDecl 0),
   .rule seed, .run "seed"]

private def declaredA : Database :=
  { Database.empty with sig := Function.update Database.empty.sig "A" (some (ctorDecl 0)) }
private def declaredAB : Database :=
  { declaredA with sig := Function.update declaredA.sig "B" (some (ctorDecl 0)) }
private def declared : Database :=
  { declaredAB with sig := Function.update declaredAB.sig "C" (some (ctorDecl 0)) }
private def registered : Database := { declared with rules := {seed} }
def reached : Database := RunRules "seed" registered

private theorem constructors : declared.sig.AllConstructors := by
  intro f
  by_cases hc : f = "C"
  · subst f; rfl
  · by_cases hb : f = "B"
    · subst f; rfl
    · by_cases ha : f = "A"
      · subst f; rfl
      · simp [declared, declaredAB, declaredA, Database.empty, Signature.mergeOf,
          hc, hb, ha]

private theorem normal {d : Database} (hc : d.sig.AllConstructors) : MergeNormal d := by
  intro row hr
  obtain ⟨dc, hd, hm, _⟩ := hr.1
  exact (hm (by simpa [Signature.mergeOf, hd] using hc row.name)).elim

private theorem empty_normal {d : Database} (he : d.eqs = ∅) : MergeNormal d := by
  intro row hr
  exact (he ▸ hr.2).elim

theorem source_reached : ProgramStep Database.empty program reached := by
  have hregister : CmdStep declared (.rule seed) registered := by
    apply CmdStep.of_reach
    · simp [cmdReach, registered, declared, declaredAB, declaredA, Database.empty]
    · exact normal constructors
  exact .cons (.of_reach rfl (empty_normal rfl))
    (.cons (.of_reach rfl (empty_normal rfl))
      (.cons (.of_reach rfl (empty_normal rfl))
        (.cons hregister
          (.cons (.of_reach rfl (normal constructors)) .nil))))

theorem source_fragment : program.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide⟩
  intro n hn
  have hnames : ∀ n ∈ program.names, ¬ "@".isPrefixOf n := by
    simp only [String.isPrefixOf, String.startsWith_string_iff]
    decide
  exact hnames n hn

private theorem seed_assertions : (b, c) ∈ reached.eqs ∧ (a, b) ∈ reached.eqs := by
  have hc : ((registered.addEq b c).addEq a b).Contained reached :=
    Database.Contained.mem_sUnion ⟨seed, by simp [registered], rfl,
      [], ValidQuerySubst.nil_iff.mpr rfl, rfl⟩
  exact ⟨hc.eqs (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
    hc.eqs (Set.mem_insert _ _)⟩

/-- The initialization rule remains registered, and every later firing is absorbed. -/
theorem source_round_idempotent (R : RulesetName) : RunRules R reached = reached := by
  apply (runRules_eq_self_iff R reached).mpr
  intro r hr _ out hout
  have hr : r = seed := by simpa [reached, RunRules, registered] using hr
  subst r
  obtain ⟨σ, _, hf⟩ := hout
  have he : evalLocalActions reached seed.actions σ =
      some ((reached.addEq b c).addEq a b) := rfl
  rw [he] at hf
  obtain rfl := Option.some.inj hf
  constructor
  rintro p (rfl | rfl | hp)
  · exact seed_assertions.2
  · exact seed_assertions.1
  · exact hp

theorem source_saturated (R : RulesetName) : RunSaturated R reached := by
  have hn : MergeNormal reached := normal constructors
  refine ⟨hn, reached, ?_, Database.SameMeaning.refl _⟩
  change MergeNormalize (RunRules R reached) reached
  rw [source_round_idempotent R]
  exact ⟨.refl, hn⟩

def oldRow : Term := .app ufName [c, b]
def newRow : Term := .app ufName [c, a]
private def compiledIndex (origin : RuleOrigin) : Nat :=
  (((compile program).zipIdx.find? fun entry =>
    decide (entry.1.ruleOrigin = some origin)).map Prod.snd).getD 0

def oldCertificate : Provenance.Proof := .rule oldRow (compiledIndex (.source 3)) [] []
def linkCertificate : Provenance.Proof :=
  .rule (.app ufName [b, a]) (compiledIndex (.source 3)) [] []
def compressedCertificate : Provenance.Proof :=
  .rule newRow (compiledIndex (.rebuild .compress))
    [("@a", c), ("@b", b), ("@c", a)] [oldCertificate, linkCertificate]
def mergedCertificate : Provenance.Proof :=
  .merge (.app ufName [b, a]) ufName oldCertificate compressedCertificate

set_option maxHeartbeats 2000000 in
-- Kernel reduction computes the compiled program and the complete certificate tree.
theorem old_certificate_accepted :
    check (Congruence.encode program) oldCertificate = some oldRow := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction computes the compiled program and the complete certificate tree.
theorem compressed_certificate_accepted :
    check (Congruence.encode program) compressedCertificate = some newRow := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction computes the compiled program and the complete certificate tree.
theorem merged_certificate_accepted :
    check (Congruence.encode program) mergedCertificate = some (.app ufName [b, a]) := by
  decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks both input certificate trees before rejecting this collision.
theorem duplicate_merge_rejected :
    check (Congruence.encode program)
      (.merge newRow ufName oldCertificate oldCertificate) = none := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks both input certificate trees before rejecting this collision.
theorem different_keys_merge_rejected :
    check (Congruence.encode program)
      (.merge newRow ufName oldCertificate linkCertificate) = none := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the premise certificate and generated matching conditions.
theorem missing_premise_rejected :
    check (Congruence.encode program)
      (.rule newRow (compiledIndex (.rebuild .compress))
        [("@a", c), ("@b", b), ("@c", a)] [oldCertificate]) = none := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks both premise certificates and generated matching conditions.
theorem mismatched_premises_rejected :
    check (Congruence.encode program)
      (.rule newRow (compiledIndex (.rebuild .compress))
        [("@a", c), ("@b", b), ("@c", a)] [linkCertificate, oldCertificate]) = none := by
  decide

theorem old_certificate_source_equality : reached.Infers c b :=
  Generated.check_uf_infers source_fragment source_reached source_saturated old_certificate_accepted

theorem compressed_certificate_source_equality : reached.Infers c a :=
  Generated.check_uf_infers source_fragment source_reached source_saturated
    compressed_certificate_accepted

theorem merged_certificate_source_equality : reached.Infers b a :=
  Generated.check_uf_infers source_fragment source_reached source_saturated
    merged_certificate_accepted

def before : Database :=
  ((Generated.emptyWorld program).addTerm oldRow).addTerm newRow
private def erased : Database :=
  (before.eraseEntry (Live.ufEntry c b)).eraseEntry (Live.ufEntry c a)
def after : Database :=
  ((erased.putEntry (Live.ufEntry b a)).putEntry (Live.ufEntry a a)).putEntry
    (Live.ufEntry c a)

private theorem uf_decl : before.sig ufName = some (tableDecl 1) :=
  encodeSig_ufName source_fragment
private theorem a_value : a.IsValue before.sig := by decide
private theorem b_value : b.IsValue before.sig := by decide
private theorem c_value : c.IsValue before.sig := by decide

theorem old_row_present : oldRow ∈ before.terms :=
  (Database.Contained.addTerm _ _).terms (Database.mem_addTerm _ _)

theorem new_row_present : newRow ∈ before.terms := Database.mem_addTerm _ _

private theorem before_wf : before.WF :=
  ((Generated.World.empty source_fragment reached).runtime.wf.addTerm _).addTerm _

theorem genuine_merge : MergeStep before after := by
  have ho : Live.ufEntry c b ∈ before.entries :=
    ⟨Live.ufEntry_valid uf_decl c_value b_value,
      Set.mem_insert_of_mem _ (Set.mem_insert _ _)⟩
  have hn : Live.ufEntry c a ∈ before.entries :=
    ⟨Live.ufEntry_valid uf_decl c_value a_value, Set.mem_insert _ _⟩
  have hbody := Live.eval_mergeBody (d := erased) uf_decl b a b_value a_value
  have hleast : Term.least b a = a := by decide
  rw [hleast] at hbody
  refine .collide ho hn (by decide) rfl uf_decl ?_ (.changed rfl ?_ hbody ?_)
  · exact .cons (before_wf.subtermClosed _ old_row_present
      (Term.arg_subterms (by simp) (.refl _))) .nil
  · change [b].take 1 ≠ [a].take 1
    decide
  · decide

theorem old_row_consumed : oldRow ∉ after.terms := by
  intro ht
  rw [Database.mem_terms_iff] at ht
  simp only [Term.mem_subterms, ← Term.mem_subtermList] at ht
  simp [after, erased, before, Generated.emptyWorld, Database.empty,
    Database.putEntry, Database.addTerm, Database.eraseEntry,
    oldRow, newRow, Live.ufEntry, Entry.atom, Entry.columns,
    a, b, c, ufName, and_or_left, or_and_right] at ht
  aesop

theorem surviving_row_present : newRow ∈ after.terms := Database.mem_addTerm _ _

/-- A consumed nonreflexive UF row retains its checked source equality. -/
theorem consumed_certificate_sound :
    MergeStep before after ∧ oldRow ∈ before.terms ∧ oldRow ∉ after.terms ∧
      check (Congruence.encode program) oldCertificate = some oldRow ∧
      c ≠ b ∧ reached.Infers c b :=
  ⟨genuine_merge, old_row_present, old_row_consumed, old_certificate_accepted,
    by decide, old_certificate_source_equality⟩

end Egglog.Tests.GeneratedProvenance
