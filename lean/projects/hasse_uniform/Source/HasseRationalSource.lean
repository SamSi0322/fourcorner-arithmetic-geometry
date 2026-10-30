import FourCorner.HasseNormsInterface
import CompleteSource11

/-! Exact rational boundary and affine-source bridges for §05.
No Brauer class, Hilbert symbol, obstruction bit or exclusion theorem is assumed.
The source predicates are imported unchanged from the byte-pinned slot11 source.
-/
namespace FourCorner.HasseRationalSource

open CompleteSource11

/-- Nonzero homogeneous rational coordinate witnesses for the displayed C_p.
This admits every projective coordinate hyperplane before boundary exclusion. -/
structure HomogeneousPoint (p : ℚ) where
  Z : ℚ
  U : ℚ
  V : ℚ
  W : ℚ
  T : ℚ
  nonzero : ¬ (Z=0 ∧ U=0 ∧ V=0 ∧ W=0 ∧ T=0)
  equations : Source p Z U V W T

private theorem two_anisotropic (x y : ℚ) (h : x^2=2*y^2) : y=0 := by
  by_contra hy
  have hns : ¬ IsSquare (2 : ℚ) := by norm_num
  apply hns
  refine ⟨x/y, ?_⟩
  field_simp
  linear_combination -h

/-- Every rational point is in the strict nonzero-coordinate domain.
In particular no boundary point is lost in the finite-rho parametrization. -/
theorem coordinates_ne_zero (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) :
    P.Z ≠ 0 ∧ P.U ≠ 0 ∧ P.V ≠ 0 ∧ P.W ≠ 0 ∧ P.T ≠ 0 := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  have hb0 : p+1 ≠ 0 := by linarith
  obtain ⟨hDU,hDW⟩ := omission_equations p P.Z P.U P.V P.W P.T hp0 P.equations
  have hnon : ¬ (P.Z=0 ∧ P.V=0 ∧ P.W=0 ∧ P.T=0) := by
    rintro ⟨hz,hv,hw,ht⟩
    exact P.nonzero ⟨hz,omission_U_no_basepoint p P.Z P.U P.V P.W P.T
      ha0 P.equations hz hv hw ht,hv,hw,ht⟩
  obtain ⟨hz,hw⟩ := HasseNormWitness.omission_denominators p P.Z P.V P.W P.T
    ha0 hb0 (by norm_num) hnon hDU.1 hDU.2
  have ht : P.T ≠ 0 := by
    intro ht
    have hpos : 0 < p*P.Z^2 := mul_pos (by linarith) (sq_pos_of_ne_zero hz)
    have hh := hDU.1
    rw [ht] at hh
    nlinarith [sq_nonneg P.V]
  have hu : P.U ≠ 0 := by
    intro hu
    have hpos : 0 < (p-1)*(p*P.Z^2) :=
      mul_pos (by linarith) (mul_pos (by linarith) (sq_pos_of_ne_zero hz))
    have hnonneg : 0 ≤ p*P.V^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hh := P.equations.1
    rw [hu] at hh
    nlinarith
  have hv : P.V ≠ 0 := by
    intro hv
    have hrel : P.U^2=p*P.Z^2 := by
      have hh := P.equations.1
      rw [hv] at hh
      nlinarith
    have he : P.T^2=2*P.U^2 := by
      have hh := hDU.1
      rw [hv] at hh
      linear_combination (-1/2 : ℚ)*hh - 2*hrel
    exact hu (two_anisotropic P.T P.U he)
  exact ⟨hz,hu,hv,hw,ht⟩

/-- Normalize the genuine homogeneous point at Z and recover all four
nonzero squares, with rho outside precisely the three excluded finite values. -/
noncomputable def toLocalPoint (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) :
    HasseNorms.LocalPoint ℚ p := by
  obtain ⟨hz,hu,hv,hw,ht⟩ := coordinates_ne_zero p hp P
  have hp0 : p ≠ 0 := by linarith
  obtain ⟨hU,hV,hW,hT⟩ := four_ordered_squares p P.Z P.U P.V P.W P.T hp0 hz P.equations
  have hr0 : P.U^2/(p*P.Z^2) ≠ 0 := div_ne_zero (pow_ne_zero _ hu)
    (mul_ne_zero hp0 (pow_ne_zero _ hz))
  have hr1 : P.U^2/(p*P.Z^2) ≠ 1 := by
    intro hh
    rw [hh] at hV
    simp only [sub_self,mul_zero] at hV
    exact (div_ne_zero hv hz) (sq_eq_zero_iff.mp hV)
  have hrm : P.U^2/(p*P.Z^2) ≠ -1 := by
    intro hh
    rw [hh] at hW
    have hh0 : (P.W/P.Z)^2=0 := by simpa only [neg_add_cancel,mul_zero] using hW
    exact (div_ne_zero hw hz) (sq_eq_zero_iff.mp hh0)
  exact ⟨P.U^2/(p*P.Z^2),P.U/P.Z,P.V/P.Z,P.W/P.Z,P.T/P.Z,
    hr0,hr1,hrm,div_ne_zero hu hz,div_ne_zero hv hz,div_ne_zero hw hz,
    div_ne_zero ht hz,hU,hV,hW,hT⟩

/-- The converse uses Z=1 and exactly the original three homogeneous equations. -/
def ofLocalPoint (p : ℚ) (S : HasseNorms.LocalPoint ℚ p) : HomogeneousPoint p :=
  ⟨1,S.u,S.v,S.w,S.t,by simp,HasseNorms.local_full_equations p S⟩

/-- This equivalence concerns the entire rational source, including the
coordinate boundary, rather than a chosen affine open assumed nonempty. -/
theorem homogeneous_nonempty_iff_localPoint (p : ℚ) (hp : 1<p) :
    Nonempty (HomogeneousPoint p) ↔ Nonempty (HasseNorms.LocalPoint ℚ p) :=
  ⟨fun ⟨P⟩ => ⟨toLocalPoint p hp P⟩,fun ⟨S⟩ => ⟨ofLocalPoint p S⟩⟩

theorem homogeneous_nonempty_iff_literal_squares (p : ℚ) (hp : 1<p) :
    Nonempty (HomogeneousPoint p) ↔ HasseNormsInterface.LocalSquares ℚ p := by
  rw [homogeneous_nonempty_iff_localPoint p hp,
    HasseNormsInterface.localPoint_iff_localSquares]

#print axioms coordinates_ne_zero
#print axioms toLocalPoint
#print axioms ofLocalPoint
#print axioms homogeneous_nonempty_iff_localPoint
#print axioms homogeneous_nonempty_iff_literal_squares

end FourCorner.HasseRationalSource
