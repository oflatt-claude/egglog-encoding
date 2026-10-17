import EgglogSemantics.Proofs.Step

/-! Monotonicity of mathematical table lookup. -/

namespace Egglog

/-! ### Reading a table -/
namespace Database
/-- `vs` are outputs `db` records for `f` at the class of the key `as`: a lookup searches
the key's congruence class rather than the term set, and a class may record several. -/
def Out (db : Database) (f : FnName) (as : List Term) (vs : List Term) : Prop :=
  ∃ bs, CongList db as bs ∧ Entry.mk f bs vs ∈ db.entries

end Database

/-- Lookup persists when assertions grow at a fixed signature. -/
theorem Database.Out.mono {d₁ d₂ : Database} (h : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  exact ⟨bs, CongList.mono h hl, ⟨hsig ▸ hrow.1, h.eqs hrow.2⟩⟩

end Egglog
