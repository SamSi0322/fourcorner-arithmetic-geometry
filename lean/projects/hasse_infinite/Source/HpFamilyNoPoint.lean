import HpConicObstruction

namespace FourCorner.HpFamilyNoPoint

open HasseNorms HasseRationalSource HasseProjectivePoint

/-- The literal rational four-square source maps injectively to every
characteristic-zero field, preserving every nonzero and excluded-rho guard. -/
noncomputable def mapLocalPoint (K : Type*) [Field K] [CharZero K]
    (p : ℚ) (S : LocalPoint ℚ p) : LocalPoint K (p : K) where
  rho := (S.rho : K)
  u := (S.u : K)
  v := (S.v : K)
  w := (S.w : K)
  t := (S.t : K)
  rho_ne_zero := by exact_mod_cast S.rho_ne_zero
  rho_ne_one := by exact_mod_cast S.rho_ne_one
  rho_ne_neg_one := by exact_mod_cast S.rho_ne_neg_one
  u_ne_zero := by exact_mod_cast S.u_ne_zero
  v_ne_zero := by exact_mod_cast S.v_ne_zero
  w_ne_zero := by exact_mod_cast S.w_ne_zero
  t_ne_zero := by exact_mod_cast S.t_ne_zero
  sqU := by exact_mod_cast S.sqU
  sqV := by exact_mod_cast S.sqV
  sqW := by exact_mod_cast S.sqW
  sqT := by exact_mod_cast S.sqT

theorem rational_source_gives_Loc (p : ℚ) (S : LocalPoint ℚ p) : Loc p := by
  refine ⟨⟨mapLocalPoint ℝ p S⟩,?_⟩
  intro q hq
  exact ⟨mapLocalPoint ℚ_[q] p S⟩

/-- Unconditional rational-point exclusion for every displayed family
parameter. Loc is derived from the supposed rational point, not assumed as
an extra family hypothesis or confused with independently proved local solubility. -/
theorem family_no_rational_point (j : ℕ) : IsEmpty (RationalPoint (HpInfiniteArithmetic.p j)) := by
  refine ⟨fun Q => ?_⟩
  let p := HpInfiniteArithmetic.p j
  have hp : 1<p := HpInfiniteArithmetic.p_gt_one j
  let S := toLocalPoint p hp (toHomogeneousPoint p Q)
  have hL := rational_source_gives_Loc p S
  exact (HasseUniformNoPoint.hp_uniform p hp (HpConicObstruction.family_domain j) hL
    (HpConicObstruction.family_T_one j)).false Q

theorem family_no_rational_homogeneous_tuple (j : ℕ) :
    ¬ ∃ Z U V W T : ℚ, ¬(Z=0 ∧ U=0 ∧ V=0 ∧ W=0 ∧ T=0) ∧
      CompleteSource11.Source (HpInfiniteArithmetic.p j) Z U V W T := by
  rintro ⟨Z,U,V,W,T,hn,hEq⟩
  let P : HomogeneousPoint (HpInfiniteArithmetic.p j) := ⟨Z,U,V,W,T,hn,hEq⟩
  exact (family_no_rational_point j).false (ofHomogeneousPoint _ P)

#print axioms rational_source_gives_Loc
#print axioms family_no_rational_point
#print axioms family_no_rational_homogeneous_tuple

end FourCorner.HpFamilyNoPoint
