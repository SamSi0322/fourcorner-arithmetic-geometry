import ThetaCoverClassPortable.SmoothProperClosedPointPlaces
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.NativeCurveGlobalConstants
open SmoothProperClosedPointPlaces

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
  [SmoothOfRelativeDimension 1 c] [IsProper c]

local instance top_nonempty : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

theorem global_germ_mem_lSpace_zero (s : Γ(X, ⊤)) :
    letI := fieldAlgebra c
    X.germToFunctionField ⊤ s ∈ LSpace (0 : Divisor K X.functionField) := by
  letI := fieldAlgebra c
  intro v
  obtain ⟨x, rfl⟩ := placeOfClosedPoint_surjective c v
  have hm : X.germToFunctionField ⊤ s ∈
      (placeOfClosedPoint c x).toValuationSubring.toSubring := by
    rw [← range_stalk c x]
    exact ⟨X.presheaf.germ ⊤ x.val trivial s,
      X.algebraMap_germ_eq_germToFunctionField (U:=⊤) (x:=x.val) trivial s⟩
  simpa using (placeOfClosedPoint c x).adicValuation_le_one_of_mem hm

theorem global_germ_algebraMap (a : K) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
    letI := fieldAlgebra c
    X.germToFunctionField ⊤ (algebraMap K Γ(X, ⊤) a)=
      algebraMap K X.functionField a := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
  letI := fieldAlgebra c
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  rw [show c.appLE ⊤ ⊤ le_top=c.appTop by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]]
  rfl

/-- Genuine global sections on the same native curve are the base field
when its actual function-field constants are the base field. -/
theorem global_sections_bijective
    (hconstants : letI := fieldAlgebra c; ConstantsAreBase K X.functionField) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
    Function.Bijective (algebraMap K Γ(X, ⊤)) := by
  letI := fieldAlgebra c
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
  constructor
  · intro a b hab
    apply (algebraMap K X.functionField).injective
    rw [← global_germ_algebraMap c a, ← global_germ_algebraMap c b, hab]
  · intro s
    have hs := global_germ_mem_lSpace_zero c s
    rw [hconstants] at hs
    obtain ⟨a, ha⟩ := hs
    refine ⟨a, X.germToFunctionField_injective ⊤ ?_⟩
    rw [global_germ_algebraMap]
    exact ha

#print axioms global_germ_mem_lSpace_zero
#print axioms global_germ_algebraMap
#print axioms global_sections_bijective
end FourCorner.NativeCurveGlobalConstants
