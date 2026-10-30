import GeometricFrobeniusTransport
import ResidueConstantFieldComparison
import ResidueFullConstants

noncomputable section
open scoped TensorProduct
namespace FourCorner.ResidueFrobeniusData
variable (k L : Type*) [Field k] [Fintype k] [Field L]
  [NeZero (2 : k)] [NeZero (2 : L)] [Algebra k L]
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev originalField (t κ : k) := CommonGenus17Field.field k t κ
abbrev geometricField (t κ : k) := CommonGenus17Field.field L (algebraMap k L t) (algebraMap k L κ)

def imageHom {t κ : k} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    originalField k t κ →+* geometricField k L t κ := by
  letI := ResidueGeometricField.all_constants_domain k L h0 h1 hm hκ
  exact GeometricTensorFrobenius.imageHom k L _ _
    (ResidueConstantFieldComparison.fractionFieldEquiv k L h0 h1 hm hκ)

abbrev imageAlgebra {t κ : k} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    Algebra (originalField k t κ) (geometricField k L t κ) :=
  (imageHom k L h0 h1 hm hκ).toAlgebra

def geometricFrobenius {t κ : k} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    geometricField k L t κ →ₐ[L] geometricField k L t κ := by
  letI := ResidueGeometricField.all_constants_domain k L h0 h1 hm hκ
  exact GeometricTensorFrobenius.transportedFrobenius k L _ _
    (ResidueConstantFieldComparison.fractionFieldEquiv k L h0 h1 hm hκ)

/-- Actual generation of the literal geometric five-root field by constants
and the original field image, with the image algebra chosen explicitly. -/
theorem generation {t κ : k} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := imageAlgebra k L h0 h1 hm hκ
    IntermediateField.adjoin L (Set.range (algebraMap (originalField k t κ) (geometricField k L t κ))) = ⊤ := by
  letI := ResidueGeometricField.all_constants_domain k L h0 h1 hm hκ
  letI := imageAlgebra k L h0 h1 hm hκ
  change IntermediateField.adjoin L (Set.range (imageHom k L h0 h1 hm hκ)) = ⊤
  exact GeometricTensorFrobenius.image_generates k L _ _
    (ResidueConstantFieldComparison.fractionFieldEquiv k L h0 h1 hm hκ)

/-- The geometric Frobenius square on every original field element is proved
from the actual tensor construction, not given as input to a Hasse bound. -/
theorem frobenius_original {t κ : k} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := imageAlgebra k L h0 h1 hm hκ
    ∀ x : originalField k t κ,
      geometricFrobenius k L h0 h1 hm hκ (algebraMap (originalField k t κ) (geometricField k L t κ) x) =
        algebraMap (originalField k t κ) (geometricField k L t κ) (x^(Nat.card k)) := by
  letI := ResidueGeometricField.all_constants_domain k L h0 h1 hm hκ
  letI := imageAlgebra k L h0 h1 hm hκ
  intro x
  change geometricFrobenius k L h0 h1 hm hκ (imageHom k L h0 h1 hm hκ x) =
    imageHom k L h0 h1 hm hκ (x^(Nat.card k))
  exact GeometricTensorFrobenius.transportedFrobenius_image k L _ _
    (ResidueConstantFieldComparison.fractionFieldEquiv k L h0 h1 hm hκ) x

theorem original_generators (t κ : k) :
    ∃ s : Finset (originalField k t κ), IntermediateField.adjoin k (s : Set (originalField k t κ)) = ⊤ := by
  change (⊤ : IntermediateField k (originalField k t κ)).FG
  exact IntermediateField.fg_top_iff.mpr (ResidueRadicalField.essFiniteType k t κ)

end FourCorner.ResidueFrobeniusData
#print axioms FourCorner.ResidueFrobeniusData.generation
#print axioms FourCorner.ResidueFrobeniusData.frobenius_original
#print axioms FourCorner.ResidueFrobeniusData.original_generators
