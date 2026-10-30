import InfinityHenselRealization
import InfinityResidueChart
import IntegralCoefficientInverse
import ResidueCoefficientInstances

noncomputable section
open AlgebraicCurve
namespace FourCorner.InfinityPlaceRealization
open RadicalLinearization ResiduePlaceEvaluation
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- A chosen actual rational place at infinity supplies the precise unit
residues needed by the genuine p-adic infinity chart. -/
theorem realize (hp : p ≠ 2) (t κ : ℚ) (hκ : κ ≠ 0) (T K : ℤ_[p])
    (hT : (T : ℚ_[p]) = t) (hK : (K : ℚ_[p]) = κ)
    (ht0 : PadicInt.toZMod T ≠ 0) (ht1 : PadicInt.toZMod (T-1) ≠ 0)
    (htm : PadicInt.toZMod (T+1) ≠ 0) (hk : PadicInt.toZMod K ≠ 0) :
    letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
    ∀ (w : Place (ZMod p) (CommonGenus17Field.field (ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)))
      (hw : w.IsRational), ell (ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K) ∉ w.toValuationSubring →
    ∃ (e : ℚ_[p]) (r : Fin 5 → ℚ_[p]), Transcendental ℚ e ∧
      ∀ i, r i^2 = values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) e i := by
  letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
  letI : NeZero (2 : ZMod p) := ⟨Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)⟩
  intro w hw hl
  have h1 : PadicInt.toZMod T ≠ 1 := by intro h; apply ht1; simp only [map_sub,map_one,h,sub_self]
  have hm : PadicInt.toZMod T ≠ -1 := by intro h; apply htm; simp only [map_add,map_one,h,neg_add_cancel]
  obtain ⟨hord,hzero,hdata⟩ := InfinityResidueChart.infinity_chart ht0 h1 hm hk w hw hl
  obtain ⟨KI,hKI,hKIf,hKIr⟩ := IntegralCoefficientInverse.exists_inverse K hk
  apply InfinityHenselRealization.realize hp t κ hκ T K KI hT hK (hKIf.trans (congrArg Inv.inv hK))
  · intro i
    have hconst : PadicInt.toZMod (InfinityHenselRealization.constantValues T K i) =
        InfinityResidueChart.residueValues (PadicInt.toZMod T) (PadicInt.toZMod K) i := by
      fin_cases i <;> simp only [InfinityHenselRealization.constantValues,InfinityResidueChart.residueValues,
        map_neg,map_sub,map_add,map_one]
    rw [hconst,←(hdata i).2.2.2]
    exact pow_ne_zero _ (hdata i).2.2.1
  · intro i
    have hconst : PadicInt.toZMod (InfinityHenselRealization.constantValues T K i) =
        InfinityResidueChart.residueValues (PadicInt.toZMod T) (PadicInt.toZMod K) i := by
      fin_cases i <;> simp only [InfinityHenselRealization.constantValues,InfinityResidueChart.residueValues,
        map_neg,map_sub,map_add,map_one]
    rw [hconst,←(hdata i).2.2.2]
    exact IsSquare.sq _

end FourCorner.InfinityPlaceRealization
#print axioms FourCorner.InfinityPlaceRealization.realize
