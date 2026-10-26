import ThetaOppositeComparison
import ThetaSourceSmooth
import ThetaProjEquality
noncomputable section
namespace FourCorner.ThetaSourceComparison
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaOppositeComparison
variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

def toOpposite : C k ⟶ OppositeProjective.curve (1:k) 5 :=
  Proj.map (forward (k:=k)) (ProjectiveClosedImmersion.irrelevant_le_map_of_surjective (forward (k:=k)) (forward_surjective (k:=k)))
def fromOpposite : OppositeProjective.curve (1:k) 5 ⟶ C k :=
  Proj.map (backward (k:=k)) (ProjectiveClosedImmersion.irrelevant_le_map_of_surjective (backward (k:=k)) (backward_surjective (k:=k)))
lemma hom_inv : toOpposite (k:=k) ≫ fromOpposite = 𝟙 _ := by
  unfold toOpposite fromOpposite
  rw [←Proj.map_comp]
  exact ThetaProjEquality.map_eq_id _ (forward_backward (k:=k)) _
lemma inv_hom : fromOpposite (k:=k) ≫ toOpposite = 𝟙 _ := by
  unfold toOpposite fromOpposite
  rw [←Proj.map_comp]
  exact ThetaProjEquality.map_eq_id _ (backward_forward (k:=k)) _
/-- An actual global projective-scheme comparison retaining [P:Q:R:7z:T]. -/
def sourceIso : C k ≅ OppositeProjective.curve (1:k) 5 :=
  ⟨toOpposite,fromOpposite,hom_inv,inv_hom⟩
lemma rational_base_unique {X : Scheme} (f g : X ⟶ Spec (.of ℚ)) : f=g := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _
lemma sourceIso_over : (sourceIso (k:=ℚ)).hom ≫ OppositeProjective.toBase (1:ℚ) 5=cToBase ℚ :=
  rational_base_unique _ _
theorem source_integral : IsIntegral (C ℚ) := by
  haveI := OppositeProjective.PostIntegral.rational_literal_projective_integral
    (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  exact IsIntegral.of_isIso (sourceIso (k:=ℚ)).inv
end FourCorner.ThetaSourceComparison
#print axioms FourCorner.ThetaSourceComparison.sourceIso
#print axioms FourCorner.ThetaSourceComparison.sourceIso_over
#print axioms FourCorner.ThetaSourceComparison.source_integral
