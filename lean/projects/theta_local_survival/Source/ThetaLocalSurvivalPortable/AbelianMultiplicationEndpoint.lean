import ThetaLocalSurvivalPortable.ActualMultiplicationFiniteEtale
import Mathlib.AlgebraicGeometry.Group.Smooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj
namespace FourCorner.ThetaLocalSurvival.Multiplication

/-- Actual abelian varieties are expressed by native proper geometrically
integral group schemes over QQ. Native group-scheme results supply both
commutativity and smoothness; [m] is proved finite etale for every m≥1. -/
theorem abelian_variety_multiplication_finite_etale (G : Over base) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] (m : ℕ) (hm : 1≤m) :
    IsFinite (multiplication G m) ∧ Etale (multiplication G m) := by
  letI : IsCommMonObj G := abelian_variety_commutative G
  letI : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  letI : Smooth G.hom := smooth_of_grpObj G.hom
  exact multiplication_finite_etale G m (lt_of_lt_of_le Nat.zero_lt_one hm)

/-- Finite etaleness of the literal multiplication pullback projection. -/
theorem abelian_cover_finite_etale (G X : Over base) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] (a : X ⟶ G) (m : ℕ) (hm : 1≤m) :
    IsFinite (pullback.fst a.left (multiplication G m)) ∧
      Etale (pullback.fst a.left (multiplication G m)) := by
  obtain ⟨hf,he⟩ := abelian_variety_multiplication_finite_etale G m hm
  letI := hf
  letI := he
  exact ⟨inferInstance,inferInstance⟩

/-- The exact algebraic cover and the actual rational origin required
by local survival, with both projection equations. -/
theorem actual_abelian_cover (G X : Over base) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] (a : X ⟶ G)
    (O : rationalBase ⟶ X) (hO : O ≫ a=1) (m : ℕ) (hm : 1≤m) :
    IsFinite (pullback.fst a.left (multiplication G m)) ∧
    Etale (pullback.fst a.left (multiplication G m)) ∧
    ∃z : base ⟶ cover G X a m,
      z ≫ pullback.fst a.left (multiplication G m)=O.left ∧
      z ≫ pullback.snd a.left (multiplication G m)=zeroPoint G ∧
      z ≫ pullback.fst a.left (multiplication G m) ≫ X.hom=𝟙 base := by
  obtain ⟨hf,he⟩ := abelian_cover_finite_etale G X a m hm
  refine ⟨hf,he,originLift G X a O hO m,originLift_fst G X a O hO m,originLift_snd G X a O hO m,?_⟩
  rw [←Category.assoc,originLift_fst]
  exact O.w

end FourCorner.ThetaLocalSurvival.Multiplication
