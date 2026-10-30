import CommonExclusion
import CommonFamilyRank
import FamilyConstituents
import ActualRealPoint08

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.CommonInfinite
open CommonLiteralField RealFieldEmbedding08 ActualRealPoint08
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- The same native normalized complete curve, at the prescribed explicit parameter. -/
abbrev familyModel (j : ℕ) (hj : 1 ≤ j) :=
  CommonSchemeModel.model (commonFamilyT j)
    (by have := (family_parameter_bounds j hj).1; linarith)
    (by have := (family_parameter_bounds j hj).1; linarith)
    (by have := (family_parameter_bounds j hj).1; linarith)

abbrev familyCurve (j : ℕ) (hj : 1 ≤ j) :=
  CommonPostFiniteP1.commonCurve (commonFamilyT j)
    (by have := (family_parameter_bounds j hj).1; linarith)
    (by have := (family_parameter_bounds j hj).1; linarith)
    (by have := (family_parameter_bounds j hj).1; linarith)
abbrev familyToBase (j : ℕ) (hj : 1 ≤ j) :=
  CommonSchemeModel.modelToBase (commonFamilyT j)
    (by have := (family_parameter_bounds j hj).1; linarith)
    (by have := (family_parameter_bounds j hj).1; linarith)
    (by have := (family_parameter_bounds j hj).1; linarith)

def familyPointOfEmbedding (j : ℕ) (hj : 1 ≤ j)
    (f : field ℚ (commonFamilyT j) →+* ℝ) : Spec (.of ℝ) ⟶ familyCurve j hj := by
  letI := CommonPostGeometricGenus.modelFieldAlgebra (commonFamilyT j)
  exact pointOfEmbedding (familyModel j hj) f

lemma familyPointOfEmbedding_over (j : ℕ) (hj : 1 ≤ j)
    (f : field ℚ (commonFamilyT j) →+* ℝ) :
    familyPointOfEmbedding j hj f ≫ familyToBase j hj =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) := by
  letI := CommonPostGeometricGenus.modelFieldAlgebra (commonFamilyT j)
  exact pointOfEmbedding_over (familyModel j hj) f

/-- The embedding coordinates used by the chamber inequalities are actual
regular-section pullbacks on neighbourhoods of that real scheme point. -/
theorem familyPointOfEmbedding_regular_value (j : ℕ) (hj : 1 ≤ j)
    (f : field ℚ (commonFamilyT j) →+* ℝ) :
    letI := CommonPostGeometricGenus.modelFieldAlgebra (commonFamilyT j)
    ∀ a : field ℚ (commonFamilyT j),
    ∃ (U : (familyCurve j hj).Opens) (hg : genericPoint (familyCurve j hj) ∈ U)
      (hx : familyPointOfEmbedding j hj f (IsLocalRing.closedPoint ℝ) ∈ U)
      (s : Γ(familyCurve j hj,U)),
      (familyCurve j hj).presheaf.germ U (genericPoint (familyCurve j hj)) hg s =
        (familyModel j hj).ffEquiv a ∧
      (Scheme.stalkClosedPointTo (familyPointOfEmbedding j hj f)).hom
        ((familyCurve j hj).presheaf.germ U _ hx s) = f a := by
  letI := CommonPostGeometricGenus.modelFieldAlgebra (commonFamilyT j)
  exact pointOfEmbedding_regular_value (familyModel j hj) f

theorem family_no_rational_points (j : ℕ) (hj : 1 ≤ j) :
    IsEmpty (Spec (.of ℚ) ⟶ familyCurve j hj) := by
  have ht := (family_parameter_bounds j hj).1
  obtain ⟨hint,hres⟩ := family_padic_parameter j hj
  apply CommonExclusion.common_exclusion ht commonSixPrimes
    commonSixPrimes_prime commonSixPrimes_injective commonSixPrimes_mod_eight
    (by rw [commonSixPrimes_prod]; norm_num) commonSixPrimes_prod_mod_eight
    ?_ CommonFamilyRank.prime_matrix_rank hint (Or.inl hres)
  refine ⟨commonFamilyScale j,ne_of_gt (commonFamilyScale_pos j hj),?_⟩
  simpa only [commonSixPrimes_prod,commonFamilyDelta] using family_discriminant_identity j hj

/-- A genuine real point of the same complete model lies in the strict return
chamber, with each literal ordered coordinate fixed by its field embedding. -/
theorem family_strict_real_point (j : ℕ) (hj : 1 ≤ j) :
    ∃ (S : CommonRootSource ℝ (commonFamilyT j : ℝ))
      (f : field ℚ (commonFamilyT j) →+* ℝ)
      (p : Spec (.of ℝ) ⟶ familyCurve j hj),
      p ≫ familyToBase j hj = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) ∧
      p = familyPointOfEmbedding j hj f ∧
      f (ell ℚ (commonFamilyT j)) = S.ell ∧
      (∀ k, f (root ℚ (commonFamilyT j) k) = sourceRoots S k) ∧
      (commonFamilyT j : ℝ)-1 < S.ell ∧ S.ell < (commonFamilyT j : ℝ)+1 ∧
      0 < S.P ∧ 0 < S.B ∧ |S.P*S.M|+|S.B*S.C| < 2 := by
  have ht := (family_parameter_bounds j hj).1
  have htop : (commonFamilyT j : ℝ) < Real.sqrt 5/2 := by
    have h : (commonFamilyT j : ℝ) < ((17/16 : ℚ) : ℝ) := by
      exact_mod_cast (family_parameter_bounds j hj).2
    norm_num at h
    exact h.trans family_upper_real
  obtain ⟨S,he,hs,hT,hP,hB,hret⟩ :=
    real_transcendental_source08 (by exact_mod_cast ht) htop
  let f := embedding (commonFamilyT j) ht S he
  exact ⟨S,f,familyPointOfEmbedding j hj f,
    familyPointOfEmbedding_over _ _ _,rfl,embedding_ell _ _ _ _,embedding_root _ _ _ _,
    hs,hT,hP,hB,hret⟩

/-- Paper cor:common-infinite and eq:common-infinite, with both point clauses
on the actual same normalized complete D_t_j, not solely on an affine equation. -/
theorem common_infinite :
    Function.Injective (fun j : {n : ℕ // 1 ≤ n} => commonFamilyT j.val) ∧
    ∀ (j : ℕ) (hj : 1 ≤ j),
      1 < commonFamilyT j ∧ commonFamilyT j < 17/16 ∧
      (17/16 : ℝ) < Real.sqrt 5/2 ∧
      IsEmpty (Spec (.of ℚ) ⟶ familyCurve j hj) ∧
      (∃ (S : CommonRootSource ℝ (commonFamilyT j : ℝ))
        (f : field ℚ (commonFamilyT j) →+* ℝ)
        (p : Spec (.of ℝ) ⟶ familyCurve j hj),
        p ≫ familyToBase j hj = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) ∧
        p = familyPointOfEmbedding j hj f ∧
        f (ell ℚ (commonFamilyT j)) = S.ell ∧
        (∀ k, f (root ℚ (commonFamilyT j) k) = sourceRoots S k) ∧
        (commonFamilyT j : ℝ)-1 < S.ell ∧ S.ell < (commonFamilyT j : ℝ)+1 ∧
        0 < S.P ∧ 0 < S.B ∧ |S.P*S.M|+|S.B*S.C| < 2) ∧
      (¬ IsSquare (commonFamilyT j+1)) ∧
      (¬ IsSquare ((commonFamilyT j+1)/2)) ∧
      commonFamilyT j^2-1 = (commonFamilyDelta : ℚ)*commonFamilyScale j^2 ∧
      commonFamilyScale j ≠ 0 ∧
      (¬ IsSquare (commonFamilyDelta : ℚ)) ∧
      (¬ IsSquare ((commonFamilyDelta : ℚ)/2)) := by
  refine ⟨family_parameter_injective,?_⟩
  intro j hj
  refine ⟨(family_parameter_bounds j hj).1,(family_parameter_bounds j hj).2,
    family_upper_real,family_no_rational_points j hj,family_strict_real_point j hj,
    family_t_add_one_not_square j hj,?_,family_discriminant_identity j hj,
    ne_of_gt (commonFamilyScale_pos j hj),family_delta_not_square,family_delta_not_twice_square⟩
  rintro ⟨r,hr⟩
  apply family_t_add_one_not_twice_square j hj
  refine ⟨r,?_⟩
  nlinarith [hr]

end FourCorner.CommonInfinite
#print axioms FourCorner.CommonInfinite.family_no_rational_points
#print axioms FourCorner.CommonInfinite.family_strict_real_point
#print axioms FourCorner.CommonInfinite.familyPointOfEmbedding_regular_value
#print axioms FourCorner.CommonInfinite.common_infinite
