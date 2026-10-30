import HpCanonicalBasis

namespace FourCorner.HpDifferentialTransport
open AlgebraicCurve
noncomputable section
variable {K F E : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [Field F] [Field E] [Algebra K F] [Algebra K E]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]
  [IsCurveOver K E] [Algebra.EssFiniteType K E]
attribute [local instance] Classical.propDecidable
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : ∀v : Place K F,v.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : ∀v : Place K E,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

theorem ramificationIndex_equiv (e : F ≃ₐ[K] E) :
    letI : Algebra F E := e.toRingHom.toAlgebra
    letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
    ∀w : Place K E,w.ramificationIndex F=1 := by
  letI : Algebra F E := e.toRingHom.toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  letI : Module.Finite F E := Module.Finite.of_surjective (Algebra.linearMap F E) e.surjective
  intro w
  obtain ⟨x,hx⟩ := e.surjective w.uniformizer
  have ho := w.ord_restrict (F := F) x
  change w.ord (e x)=_ at ho
  rw [hx,w.ord_uniformizer] at ho
  have he : (0 : ℤ)<w.ramificationIndex F := by exact_mod_cast w.ramificationIndex_pos (F := F)
  have hn : 0<(w.restrict F).ord x := by nlinarith
  have hi : (w.ramificationIndex F : ℤ)≤1 := by nlinarith
  exact_mod_cast (by omega : (w.ramificationIndex F : ℤ)=1)

/-- A genuine constant-field isomorphism preserves the intrinsic regular forms. -/
theorem pullback_regular (e : F ≃ₐ[K] E) {ω : Ω[F⁄K]} (hω : ω∈regularDifferentials K F) :
    pullbackDiff e.toAlgHom ω∈regularDifferentials K E := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  letI : Algebra F E := e.toRingHom.toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  letI : Module.Finite F E := Module.Finite.of_surjective (Algebra.linearMap F E) e.surjective
  by_cases hz : ω=0
  · simp [hz]
  intro w
  refine ⟨w.differentialCoeff (pullbackDiff e.toAlgHom ω),?_,(w.differentialCoeff_smul_dCoord _).symm⟩
  apply P2MW.S_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed.GenusRegDiffs.mem_of_ord_nonneg w
  change 0≤w.ordDifferential (KaehlerDifferential.map K K F E ω)
  rw [P2MW.S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.AlgebraicCurve.ordDifferential_map_eq
    localUnitDerivativeRegular_of_isCurveOver
    (fun v => Nat.cast_ne_zero.mpr (by rw [ramificationIndex_equiv e v];decide)) hz w,
    ramificationIndex_equiv e w]
  simp only [Nat.cast_one,one_mul,sub_self,add_zero]
  obtain ⟨f,hf,he⟩ := hω (w.restrict F)
  rw [Place.ordDifferential,(w.restrict F).differentialCoeff_unique he]
  exact P2MW.S_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed.GenusRegDiffs.ord_nonneg_of_mem _ hf

theorem pullback_injective (e : F ≃ₐ[K] E) (w : Place K E) :
    Function.Injective (pullbackDiff e.toAlgHom) := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  letI : Algebra F E := e.toRingHom.toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  letI : Module.Finite F E := Module.Finite.of_surjective (Algebra.linearMap F E) e.surjective
  letI : Algebra.IsIntegral F E := Algebra.IsIntegral.of_finite F E
  intro a b hab
  by_contra hn
  have hz : a-b ≠ 0 := sub_ne_zero.mpr hn
  have hh : pullbackDiff e.toAlgHom (a-b)=0 := by rw [map_sub,hab,sub_self]
  exact P2MW.S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.AlgebraicCurve.map_ne_zero_of_tame (K := K) (F := F) (F' := E)
    localUnitDerivativeRegular_of_isCurveOver
    (fun v => Nat.cast_ne_zero.mpr (Nat.ne_of_gt v.ramificationIndex_pos)) w hz hh

theorem pullback_smul (e : F ≃ₐ[K] E) (a : F) (ω : Ω[F⁄K]) :
    pullbackDiff e.toAlgHom (a • ω)=e a • pullbackDiff e.toAlgHom ω := by
  letI : Algebra F E := e.toRingHom.toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  exact ((KaehlerDifferential.map K K F E).map_smul a ω).trans
    (IsScalarTower.algebraMap_smul E a _).symm

#print axioms pullback_injective
#print axioms pullback_smul
#print axioms ramificationIndex_equiv
#print axioms pullback_regular
end
end FourCorner.HpDifferentialTransport
