import FiniteBranchRealization
import IntegralCoefficientInverse
import FiniteBranchCharts
import ResidueCoefficientInstances

noncomputable section
open AlgebraicCurve
namespace FourCorner.FinitePlaceRealization
open RadicalLinearization ResiduePlaceEvaluation
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Every actual rational residue place with finite ell gives a
transcendental Qp solution, preserving the SAME t,kappa and all five roots.
All five finite branch cases are included. -/
theorem realize (hp : p ≠ 2) (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (T K : ℤ_[p])
    (hT : (T : ℚ_[p]) = t) (hK : (K : ℚ_[p]) = κ)
    (ht0 : PadicInt.toZMod T ≠ 0) (ht1 : PadicInt.toZMod (T-1) ≠ 0)
    (htm : PadicInt.toZMod (T+1) ≠ 0) (hk : PadicInt.toZMod K ≠ 0) :
    letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
    ∀ (w : Place (ZMod p) (CommonGenus17Field.field (ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)))
      (hw : w.IsRational), ell (ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K) ∈ w.toValuationSubring →
    ∃ (e : ℚ_[p]) (r : Fin 5 → ℚ_[p]), Transcendental ℚ e ∧
      ∀ i, r i^2 = values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) e i := by
  letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
  letI : NeZero (2 : ZMod p) := ⟨Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)⟩
  intro w hw hl
  have h1 : PadicInt.toZMod T ≠ 1 := by intro h; apply ht1; simp only [map_sub,map_one,h,sub_self]
  have hm : PadicInt.toZMod T ≠ -1 := by intro h; apply htm; simp only [map_add,map_one,h,neg_add_cancel]
  obtain ⟨KI,hKI,hKIf,hKIr⟩ := IntegralCoefficientInverse.exists_inverse K hk
  have hKIf' : (KI : ℚ_[p]) = (κ : ℚ_[p])⁻¹ := hKIf.trans (congrArg Inv.inv hK)
  let α := evaluate w hw ⟨ell (ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K),hl⟩
  let r₀ (i : Fin 5) := evaluate w hw (FiniteResidueChart.rootSection _ _ hk w hl i)
  have hr₀ (i : Fin 5) : r₀ i^2 = values (PadicInt.toZMod T) (PadicInt.toZMod K)⁻¹ α i :=
    FiniteResidueChart.residue_equations _ _ hk w hw hl i
  by_cases hb : ∃ j, α = LinearizedFactors.branch (PadicInt.toZMod T) j
  · obtain ⟨j,hj⟩ := hb
    obtain ⟨hord,hzero,hn,hs⟩ := FiniteBranchCharts.branch_chart ht0 h1 hm hk w hw hl j hj
    apply FiniteBranchRealization.realize hp t κ ht hκ T KI hT hKIf' j r₀
    · intro i
      rw [hKIr]
      exact hs i
    · intro i hi
      exact (hn i hi).1
  · have hoff : ∀ j, α ≠ LinearizedFactors.branch (PadicInt.toZMod T) j := by
      simpa only [not_exists] using hb
    have hn := FiniteBranchCharts.ordinary_chart ht0 h1 hm hk w hw hl hoff
    obtain ⟨A,hA⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p) α
    apply FiniteHenselRealization.ordinary hp t κ T KI A hT hKIf' r₀
    · intro i
      rw [hKIr,hA]
      exact hr₀ i
    · intro i
      exact (hn i).2.1

end FourCorner.FinitePlaceRealization
#print axioms FourCorner.FinitePlaceRealization.realize
