import Mathlib.Algebra.AlgebraicCard
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Module.PerfectSpace
import GoodPrimeParameters

noncomputable section
open Set Topology
namespace FourCorner.PadicTranscendental

/-- Baire's theorem excludes the countable set of algebraic elements in
EVERY nonempty open subset; no transcendental parameter is postulated. -/
theorem dense_transcendental (L : Type*) [NontriviallyNormedField L]
    [CompleteSpace L] [CharZero L] : Dense {x : L | Transcendental ℚ x} := by
  have hd : Dense (⋂ a ∈ {x : L | IsAlgebraic ℚ x}, ({a} : Set L)ᶜ) :=
    dense_biInter_of_isOpen (fun _ _ => isOpen_compl_singleton)
      (Algebraic.countable ℚ L) (fun a _ => dense_compl_singleton a)
  apply hd.mono
  intro x hx
  simp only [mem_iInter,mem_compl_iff,mem_singleton_iff] at hx
  exact fun h => hx x h rfl

theorem exists_in_open {p : ℕ} [Fact p.Prime] {U : Set ℚ_[p]}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, Transcendental ℚ x := by
  obtain ⟨x,hx,hT⟩ := (dense_transcendental ℚ_[p]).inter_open_nonempty U hU hne
  exact ⟨x,hx,hT⟩

theorem exists_in_ball {p : ℕ} [Fact p.Prime] (a : ℚ_[p]) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Metric.ball a ε, Transcendental ℚ x :=
  exists_in_open Metric.isOpen_ball ⟨a,Metric.mem_ball_self hε⟩

end FourCorner.PadicTranscendental
#print axioms FourCorner.PadicTranscendental.dense_transcendental
#print axioms FourCorner.PadicTranscendental.exists_in_ball
