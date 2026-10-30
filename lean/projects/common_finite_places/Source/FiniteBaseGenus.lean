import OddResidueGenus
import ResidueFrobeniusData
import ResidueCoefficientInstances
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed

noncomputable section
namespace FourCorner.FiniteBaseGenus
open AlgebraicCurve
variable (k : Type*) [Field k] [Fintype k] [NeZero (2:k)]
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

/-- Actual finite-base genus of the literal five-root function field.
The constant extension embedding, its generation, geometric Frobenius square,
and full-constants property are all PROVED constituents, not hypotheses.
No assertion that all source place residue degrees are one is used. -/
theorem seventeen {t κ : k} (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) :
    genusFF k (CommonGenus17Field.field k t κ)=17 := by
  let L := AlgebraicClosure k
  let F0 := CommonGenus17Field.field k t κ
  let F := CommonGenus17Field.field L (algebraMap k L t) (algebraMap k L κ)
  letI : PerfectField k := PerfectField.ofFinite
  letI : PerfectField L := IsAlgClosed.perfectField L
  letI : NeZero (2:L) := ⟨by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k L)).mpr (NeZero.ne (2:k))⟩
  letI : Algebra F0 F := ResidueFrobeniusData.imageAlgebra k L h0 h1 hm hκ
  letI : IsCurveOver k F0 := ResidueRadicalField.isCurveOver k t κ
  letI : IsCurveOver L F := ResidueRadicalField.isCurveOver L _ _
  have hdesc := genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed k L F0 F
    (ResidueFrobeniusData.original_generators k t κ)
    (ResidueFrobeniusData.generation k L h0 h1 hm hκ)
    (ResidueFrobeniusData.geometricFrobenius k L h0 h1 hm hκ)
    (ResidueFrobeniusData.frobenius_original k L h0 h1 hm hκ)
    (ResidueFullConstants.constantsAreBase k h0 h1 hm hκ)
  have h0' : algebraMap k L t≠0 := (map_ne_zero _).mpr h0
  have h1' : algebraMap k L t≠1 := by simpa only [map_one] using (algebraMap k L).injective.ne h1
  have hm' : algebraMap k L t≠-1 := by simpa only [map_neg,map_one] using (algebraMap k L).injective.ne hm
  have hκ' : algebraMap k L κ≠0 := (map_ne_zero _).mpr hκ
  have hgeom : genusFF L F=17 := OddResidueGenus.five_genus h0' h1' hm' hκ'
  exact hdesc.symm.trans hgeom
end FourCorner.FiniteBaseGenus
#print axioms FourCorner.FiniteBaseGenus.seventeen
#check @FourCorner.FiniteBaseGenus.seventeen

namespace FourCorner.FiniteBaseGenus
open AlgebraicCurve
variable (k : Type*) [Field k] [Finite k] [NeZero (2:k)]

/-- The same endpoint needs only finiteness, not a supplied enumeration or
perfectness hypothesis on the constants. -/
theorem seventeen_of_finite {t κ : k} (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) :
    genusFF k (CommonGenus17Field.field k t κ)=17 := by
  letI : Fintype k := Fintype.ofFinite k
  exact seventeen k h0 h1 hm hκ
end FourCorner.FiniteBaseGenus
#print axioms FourCorner.FiniteBaseGenus.seventeen_of_finite
#check @FourCorner.FiniteBaseGenus.seventeen_of_finite
