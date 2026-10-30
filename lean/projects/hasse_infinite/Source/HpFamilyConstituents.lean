import HpEverywhereLocal
import HpModelNoPoint

/-! Exact arithmetic and actual-curve constituents of thm:hp-infinite.
This does NOT assert infinitely many geometric isomorphism classes. -/
namespace FourCorner.HpFamilyConstituents
open AlgebraicGeometry CategoryTheory
noncomputable section

/-- Exact displayed family: infinitely many rational parameters, original
Domain, literal thin bit, full everywhere local solubility, and no original
rational projective point. Geometric nonisomorphism is not inferred from
parameter injectivity. -/
theorem arithmetic_family :
    (Set.range HpInfiniteArithmetic.p).Infinite ∧
    ∀j : ℕ,1<HpInfiniteArithmetic.p j ∧ HasseNorms.Domain (HpInfiniteArithmetic.p j) ∧
      HasseObstructionArithmetic.T (HpInfiniteArithmetic.p j)=1 ∧
      HasseNorms.Loc (HpInfiniteArithmetic.p j) ∧
      IsEmpty (HasseProjectivePoint.RationalPoint (HpInfiniteArithmetic.p j)) := by
  refine ⟨HpInfiniteArithmetic.infinitely_many_parameters,?_⟩
  intro j
  exact ⟨HpInfiniteArithmetic.p_gt_one j,HpConicObstruction.family_domain j,
    HpConicObstruction.family_T_one j,HpEverywhereLocal.family_Loc j,
    HpFamilyNoPoint.family_no_rational_point j⟩

theorem same_model_no_rational_point (j : ℕ) :
    ¬∃f : Spec (CommRingCat.of ℚ) ⟶ HpSchemeModel.curve (HpInfiniteArithmetic.p j),
      f ≫ HpSchemeModel.toBase (HpInfiniteArithmetic.p j)=𝟙 _ :=
  HpModelNoPoint.family_no_model_point j

theorem same_model_finite_point (q : ℕ) [Fact q.Prime] (j : ℕ) :
    ∃f : Spec (CommRingCat.of ℚ_[q]) ⟶ HpSchemeModel.curve (HpInfiniteArithmetic.p j),
      f ≫ HpSchemeModel.toBase (HpInfiniteArithmetic.p j)=
        Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[q])) :=
  HpEverywhereLocal.family_model_point q j

theorem same_model_real_point (j : ℕ) :
    ∃f : Spec (CommRingCat.of ℝ) ⟶ HpSchemeModel.curve (HpInfiniteArithmetic.p j),
      f ≫ HpSchemeModel.toBase (HpInfiniteArithmetic.p j)=
        Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) :=
  HpStrictRealGeneric.family_model_real_point j

/-- The intrinsic dimension of ACTUAL global relative Kähler differentials
on the ACTUAL Qbar base change of the same smooth proper model is five. -/
theorem same_model_geometric_genus_five (j : ℕ) :
    let c := HpSchemeModel.geometricToBase (HpInfiniteArithmetic.p j)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤)=5 :=
  HpSchemeModel.geometric_globalDifferentials_five _ (HpInfiniteArithmetic.p_gt_one j)

#print axioms arithmetic_family
#print axioms same_model_no_rational_point
#print axioms same_model_finite_point
#print axioms same_model_real_point
#print axioms same_model_geometric_genus_five
end
end FourCorner.HpFamilyConstituents
