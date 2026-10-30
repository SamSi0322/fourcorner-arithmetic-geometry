import HpLiteralGeometric
import HpLiteralPoints

/-! Exact per-member conclusions of thm:hp-infinite on the ORIGINAL literal
P4 intersection. Infinitely many geometric classes is a separate theorem,
proved through native unmarked isomorphisms, not parameter injectivity. -/
namespace FourCorner.HpLiteralFamilyConstituents
open AlgebraicGeometry CategoryTheory
noncomputable section

/-- Every exact displayed parameter satisfies all original arithmetic,
local, strict real, genus, and rational-exclusion clauses on the same
literal projective C_p. No model identification is left as a premise. -/
theorem all_members (j : ℕ) :
    let p := HpInfiniteArithmetic.p j
    1<p ∧ HasseNorms.Domain p ∧ HasseObstructionArithmetic.T p=1 ∧ HasseNorms.Loc p ∧
    IsClosedImmersion (HpLiteralProjective.inclusion ℚ p) ∧
    IsIntegral (HpLiteralProjective.curve ℚ p) ∧
    IsProper (HpLiteralProjective.toBase ℚ p) ∧
    SmoothOfRelativeDimension 1 (HpLiteralProjective.toBase ℚ p) ∧
    GeometricallyConnected (HpLiteralProjective.toBase ℚ p) ∧
    (let c := HpLiteralGeometric.geometricToBase p
     letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
     Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
       Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤)=5) ∧
    (∀q : ℕ,∀[Fact q.Prime],∃f : Spec (.of ℚ_[q]) ⟶ HpLiteralProjective.curve ℚ p,
      f ≫ HpLiteralProjective.toBase ℚ p=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[q]))) ∧
    (∃S : HasseNorms.LocalPoint ℝ (p : ℝ),1<S.rho ∧
      0<2*S.t^2-4*|S.u|-|S.v*S.w| ∧
      HpLiteralPoints.point (K:=ℚ) (L:=ℝ) p S ≫ HpLiteralProjective.toBase ℚ p=
        Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ))) ∧
    (¬∃f : Spec (.of ℚ) ⟶ HpLiteralProjective.curve ℚ p,f ≫ HpLiteralProjective.toBase ℚ p=𝟙 _) := by
  let p := HpInfiniteArithmetic.p j
  have hp : 1<p := HpInfiniteArithmetic.p_gt_one j
  refine ⟨hp,HpConicObstruction.family_domain j,HpConicObstruction.family_T_one j,
    HpEverywhereLocal.family_Loc j,HpLiteralProjective.closed ℚ p,
    HpLiteralIntegral.integral ℚ p (by linarith) (by linarith) (by linarith),
    HpLiteralProjective.proper ℚ p,HpLiteralSmooth.smooth p (by linarith) (by linarith) (by linarith),
    HpLiteralGeometric.geometricallyConnected p hp,
    HpLiteralGeometric.geometric_globalDifferentials_five p hp,?_,?_,
    HpLiteralPoints.family_no_literal_point j⟩
  · intro q hq
    exact HpLiteralPoints.family_finite_point q j
  · obtain ⟨S,_,hS,hm⟩ := HpStrictRealGeneric.family_strict_real_transcendental j
    exact ⟨S,hS,hm,HpLiteralPoints.point_over p S⟩

#print axioms all_members
end
end FourCorner.HpLiteralFamilyConstituents
