import ThetaCoverClassPortable.ThetaDGenusThree
import ThetaCoverClassPortable.geometry.SchemeModelTwoAffineCover
import ThetaCoverClassPortable.ModelGenusBridge.KaehlerSheafGenus
import ThetaCoverClassPortable.RiemannRochWithGenusFF
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental

namespace FourCorner.ThetaDNativeSections
open AlgebraicGeometry AlgebraicCurve CategoryTheory IntermediateField
open ThetaDGeometricModel
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType

 def coverAlongIso {X Y : Scheme} (i : X ≅ Y) (V : Y.TwoAffineOpenCover) : X.TwoAffineOpenCover where
  U0 := i.hom ⁻¹ᵁ V.U0
  U1 := i.hom ⁻¹ᵁ V.U1
  isAffineOpen_U0 := V.isAffineOpen_U0.preimage i.hom
  isAffineOpen_U1 := V.isAffineOpen_U1.preimage i.hom
  sup_eq_top := by
    change i.hom ⁻¹ᵁ (V.U0 ⊔ V.U1)=⊤
    rw [V.sup_eq_top]
    rfl
  isAffineOpen_inf := V.isAffineOpen_inf.preimage i.hom

/-- Two real affine opens on the original geometric D, obtained through
its constructed native field model and an ACTUAL over-K isomorphism. -/
theorem exists_two_affine_cover : Nonempty geometricD.TwoAffineOpenCover := by
  obtain ⟨t,ht,hfd,_⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=field)
  letI := hfd
  have ht0 : t ≠ 0 := by intro h;rw [h] at ht;exact ht isAlgebraic_zero
  letI : Fact (t ≠ 0) := ⟨ht0⟩
  letI : FiniteDimensional K⟮t⁻¹⟯ field := by
    rw [CurveModel.adjoin_simple_inv_eq]
    infer_instance
  let M : CurveModel K field := CurveModel.ofGenerator K t ht
  letI := M.isIntegral
  letI := M.isProper
  letI := M.smooth
  letI := M.functionFieldAlgebra
  let e : M.C.functionField ≃ₐ[K] field := M.ffAlgEquiv.symm
  obtain ⟨i,hi,_⟩ := SmoothCurveExtension.iso_of_functionField_algEquiv toBase M.toBase e
  let V : M.C.TwoAffineOpenCover := SchemeModelFiniteExtension.gluedTwoAffineOpenCover K field t
  exact ⟨coverAlongIso i V⟩

 def actualCover : geometricD.TwoAffineOpenCover := Classical.choice exists_two_affine_cover

/-- Actual global relative Kahler differentials of original D_Qbar have
intrinsic dimension THREE, with the genuine structural K-module action. -/
theorem global_differentials_three :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤
    Module.Finite K Γ(toBase.kaehler,⊤) ∧ Module.finrank K Γ(toBase.kaehler,⊤)=3 := by
  obtain ⟨hf,hg⟩ := KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF actualCover toBase
  exact ⟨hf,hg.trans ThetaDGenusThree.genus_three⟩

/-- Full all-divisor Riemann-Roch on the ACTUAL native field of original
D_Qbar, now with its PROVED genus three, not a genus premise. -/
theorem all_divisor_RR :
    ∃Kc : Divisor K field,∀B : Divisor K field,
      (ell B : ℤ)-ell (Kc-B)=Divisor.degree B-2 := by
  obtain ⟨Kc,hRR⟩ := RiemannRochWithGenusFF.exists_rr (K:=K) (F:=field)
  refine ⟨Kc,fun B=>?_⟩
  have hh := hRR B
  rw [ThetaDGenusThree.genus_three] at hh
  norm_num at hh
  linarith

local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K field,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem actual_RR : FunctionFieldRiemannRoch K field := by
  obtain ⟨t,ht,hfd,_⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=field)
  exact functionFieldRiemannRoch_of_isAlgClosed_of_transcendental ht hfd

 theorem actual_constants : ConstantsAreBase K field := by
  obtain ⟨t,ht,_,_⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=field)
  exact constantsAreBase_of_isAlgClosed_of_transcendental t ht

 theorem divisor_genus_three : genus K field=3 := by
  obtain ⟨ω,hω⟩ := exists_ne (0 : Ω[field⁄K])
  have hg : genus K field=genusFF K field :=
    eq_genusFF_of_forall_ell_sub_ell_eq actual_constants (Kc:=canonicalDivisorOf hω) (g:=genus K field)
      (fun B => actual_RR hω B)
  exact hg.trans ThetaDGenusThree.genus_three

/-- All-divisor RR for EVERY ACTUAL nonzero rational differential's canonical
divisor on original D_Qbar, with the proved genus value. -/
 theorem canonical_RR {ω : Ω[field⁄K]} (hω : ω ≠ 0) (B : Divisor K field) :
    (ell B : ℤ)-ell (canonicalDivisorOf hω-B)=Divisor.degree B-2 := by
  have hh := actual_RR hω B
  rw [divisor_genus_three] at hh
  norm_num at hh
  linarith

 theorem canonical_degree_four {ω : Ω[field⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω)=4 := by
  rw [degree_canonicalDivisor_eq_of_riemannRoch actual_RR actual_constants hω,divisor_genus_three]
  norm_num

#print axioms actual_RR
#print axioms actual_constants
#print axioms divisor_genus_three
#print axioms canonical_RR
#print axioms canonical_degree_four
#print axioms exists_two_affine_cover
#print axioms global_differentials_three
#print axioms all_divisor_RR
end
end FourCorner.ThetaDNativeSections
