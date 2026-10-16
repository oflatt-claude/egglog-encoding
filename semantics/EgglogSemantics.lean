import EgglogSemantics.Proofs.Congruence.AbstractComplete
import EgglogSemantics.Proofs.Congruence.AbstractTerminationComplete
import EgglogSemantics.Proofs.Congruence.Correctness
import EgglogSemantics.Congruence.Correctness
import EgglogSemantics.Tests.Checks
import EgglogSemantics.Tests.CongruenceCorrectness
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Proofs.Congruence.Observation
import EgglogSemantics.Proofs.Congruence.AbstractMaintenance
import EgglogSemantics.Proofs.Counterexamples
import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.Lattice
import EgglogSemantics.Proofs.Merge
import EgglogSemantics.Tests.Egg
import EgglogSemantics.Tests.Parse
import EgglogSemantics.Tests.Render
import EgglogSemantics.Tests.Examples

-- Congruence compilation and its data-only correspondence reductions.
import EgglogSemantics.Tests.Congruence

-- Source proof checking and existence soundness.
import EgglogSemantics.Proofs.SourceProof.Counterexamples
import EgglogSemantics.Tests.SourceProof
import EgglogSemantics.Tests.SourceProofCorrectness

-- Function provenance and checking against the relational program.
import EgglogSemantics.Tests.Provenance
import EgglogSemantics.Proofs.Provenance.Counterexamples
import EgglogSemantics.Proofs.Provenance.Countermodel
import EgglogSemantics.Proofs.Provenance.DistinctMerge
import EgglogSemantics.Tests.Resugar

-- Current-table specification migration: pure foundations and executable regressions.
import EgglogSemantics.Proofs.OrderFinite
import EgglogSemantics.Proofs.SourceMeaning
import EgglogSemantics.Proofs.Congruence.LiveLeaders
import EgglogSemantics.Proofs.Congruence.LiveNormalization
import EgglogSemantics.Proofs.Congruence.LiveState
import EgglogSemantics.Tests.LiveCompiler
import EgglogSemantics.Tests.LeaderGrowth
import EgglogSemantics.Tests.LiveSemantics
import EgglogSemantics.Tests.MergeViews

import EgglogSemantics.Tests.AtomStore

import EgglogSemantics.Tests.SubtermExistence
