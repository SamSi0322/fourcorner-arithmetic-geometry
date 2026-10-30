import ThetaCoverClassPortable.UniversalH0AllTestSchemes
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry
/-- Actual projection H0 for all test schemes from actual universal affine H0. -/
theorem bijective_appTop_pullback_snd_of_forall_bijective_algebraMap_sections
 (R:Type u)[CommRing R]{C:Scheme.{u}}(c:C⟶Spec (.of R))
 (hH0:∀(A:Type u)[CommRing A][Algebra R A],
  letI:=Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
  Function.Bijective (algebraMap A Γ(pullback c (Scheme.TwoAffineOpenCover.specMap R A),⊤)))
 {T:Scheme.{u}}(t:T⟶Spec (.of R)):
 Function.Bijective (pullback.snd c t).appTop :=
 FourCorner.UniversalH0AllTestSchemes.bijective_appTop_pullback_snd c t hH0
#print axioms bijective_appTop_pullback_snd_of_forall_bijective_algebraMap_sections
end AlgebraicGeometry
