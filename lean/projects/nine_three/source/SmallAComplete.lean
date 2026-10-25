import FourCorner.NineSmallACoordinates
import FourCorner.NineSmallAPoints
import SplitCurveOrdered
import SignedSquareClasses
import ActualKummerFinite
import SmallTorsionBounds

open WeierstrassCurve.Affine
namespace FourCorner.NineSmallA
open OrderedSplit
noncomputable section
local instance : (splitCurve 6 8).IsElliptic :=
  splitCurve_isElliptic 6 8 (by norm_num) (by norm_num) (by norm_num)

abbrev W := (splitCurve 6 8).toAffine
abbrev δ := splitDelta 6 8 (by norm_num) (by norm_num) (by norm_num)

/-- The four supported rows, with their literal signs. -/
def rows : Fin 4 → Fin 3 → Units.modPow ℚ 2 :=
 ![ ![scalarClass 1 (by norm_num),scalarClass 1 (by norm_num),scalarClass 1 (by norm_num)],
    ![scalarClass 2 (by norm_num),scalarClass 2 (by norm_num),scalarClass 1 (by norm_num)],
    ![scalarClass 3 (by norm_num),scalarClass (-6) (by norm_num),scalarClass (-2) (by norm_num)],
    ![scalarClass 6 (by norm_num),scalarClass (-12) (by norm_num),scalarClass (-2) (by norm_num)]]

lemma scalar_eq {a b q : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (heq : a=b*q^2) :
    scalarClass a ha = scalarClass b hb :=
  (Units.modPow.signedUnits_mk0_eq_iff_exists a b ha hb).mpr ⟨q,heq⟩

lemma ordinary_image (x y : ℚ) (hxy : W.Nonsingular x y) (hy : y ≠ 0) :
    ∃ i : Fin 4, δ (Multiplicative.ofAdd (Point.some x y hxy)) = rows i := by
  have heq := (splitCurve_equation_iff 6 8 x y).mp hxy.1
  have hx : x ≠ 0 := (abscissa_pos hy heq).ne'
  have hx6 : x ≠ 6 := by intro h; subst x; norm_num at heq; exact hy heq
  have hx8 : x ≠ 8 := by intro h; subst x; norm_num at heq; exact hy heq
  rw [splitDelta_some_of_nonroot 6 8 (by norm_num) (by norm_num) (by norm_num) hxy hx hx6 hx8]
  obtain ⟨a,c,hrow,u,v,z,hu,hv,hz,h0,h6,h8⟩ := ordinary_coordinate_rows hy heq
  rcases hrow with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · refine ⟨0,?_⟩
    simp only [rows,Matrix.cons_val_zero]
    ext i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    · exact scalar_eq _ (by norm_num) (by simpa using h0)
    · exact scalar_eq _ (by norm_num) (by simpa using h6)
    · exact scalar_eq _ (by norm_num) (by simpa using h8)
  · refine ⟨1,?_⟩
    simp only [rows,Matrix.cons_val_one]
    ext i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    · exact scalar_eq _ (by norm_num) (by simpa using h0)
    · exact scalar_eq _ (by norm_num) (by simpa using h6)
    · exact scalar_eq _ (by norm_num) (by simpa using h8)
  · refine ⟨2,?_⟩
    simp only [rows,Matrix.cons_val_two]
    ext i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    · exact scalar_eq _ (by norm_num) (by simpa using h0)
    · exact scalar_eq _ (by norm_num) (by simpa using h6)
    · exact scalar_eq _ (by norm_num) (by simpa using h8)
  · refine ⟨3,?_⟩
    simp only [rows,Matrix.cons_val_three]
    ext i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    · exact scalar_eq _ (by norm_num) (by simpa using h0)
    · exact scalar_eq _ (by norm_num) (by simpa using h6)
    · exact scalar_eq _ (by norm_num) (by simpa using h8)

end
end FourCorner.NineSmallA
#print axioms FourCorner.NineSmallA.ordinary_image

namespace FourCorner.NineSmallA
open OrderedSplit
noncomputable section
local instance : (splitCurve 6 8).IsElliptic :=
  splitCurve_isElliptic 6 8 (by norm_num) (by norm_num) (by norm_num)

lemma zero_root_image (h : W.Nonsingular 0 0) :
    δ (Multiplicative.ofAdd (Point.some 0 0 h)) = rows 2 := by
  rw [splitDelta_at_zero 6 8 (by norm_num) (by norm_num) (by norm_num) h]
  ext i
  fin_cases i <;> simp only [rows,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  · exact scalar_eq _ _ (q:=4) (by norm_num)
  · exact scalar_eq _ _ (q:=1) (by norm_num)
  · exact scalar_eq _ _ (q:=2) (by norm_num)

lemma six_root_image (h : W.Nonsingular 6 0) :
    δ (Multiplicative.ofAdd (Point.some 6 0 h)) = rows 3 := by
  rw [splitDelta_at_A 6 8 (by norm_num) (by norm_num) (by norm_num) h]
  ext i
  fin_cases i <;> simp only [rows,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  · exact scalar_eq _ _ (q:=1) (by norm_num)
  · exact scalar_eq _ _ (q:=1) (by norm_num)
  · exact scalar_eq _ _ (q:=1) (by norm_num)

lemma eight_root_image (h : W.Nonsingular 8 0) :
    δ (Multiplicative.ofAdd (Point.some 8 0 h)) = rows 1 := by
  rw [splitDelta_at_B 6 8 (by norm_num) (by norm_num) (by norm_num) h]
  ext i
  fin_cases i <;> simp only [rows,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  · exact scalar_eq _ _ (q:=2) (by norm_num)
  · exact scalar_eq _ _ (q:=1) (by norm_num)
  · exact scalar_eq _ _ (q:=4) (by norm_num)

/-- The full Kummer image, including infinity and every two-torsion point,
is contained in a concrete set of four ordered rows. -/
theorem all_images (P : W.Point) : ∃ i : Fin 4, δ (Multiplicative.ofAdd P) = rows i := by
  cases P with
  | zero =>
    refine ⟨0,?_⟩
    change δ 1 = _
    rw [map_one]
    ext i
    fin_cases i <;> simp only [rows,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Pi.one_apply]
    all_goals symm; change QuotientGroup.mk (Units.mk0 (1:ℚ) _) = 1; simp
  | some x y h =>
    by_cases hy : y=0
    · subst y
      have heq := (splitCurve_equation_iff 6 8 x 0).mp h.1
      have hprod : x*(x-6)*(x-8)=0 := by linarith
      rcases mul_eq_zero.mp hprod with hp|hp
      · rcases mul_eq_zero.mp hp with hp|hp
        · subst x; exact ⟨2,zero_root_image h⟩
        · have : x=6 := by linarith
          subst x; exact ⟨3,six_root_image h⟩
      · have : x=8 := by linarith
        subst x; exact ⟨1,eight_root_image h⟩
    · exact ordinary_image x y h hy

def imageSet : Finset (Fin 3 → Units.modPow ℚ 2) := by
  classical
  exact Finset.univ.image rows
lemma imageSet_card : imageSet.card ≤ 4 := by
  classical
  change (Finset.univ.image rows).card ≤ 4
  exact (Finset.card_image_le).trans (by simp)
lemma mem_imageSet (P : W.Point) : δ (Multiplicative.ofAdd P) ∈ imageSet := by
  classical
  change δ (Multiplicative.ofAdd P) ∈ Finset.univ.image rows
  obtain ⟨i,hi⟩ := all_images P
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩

/-- The actual Mordell--Weil theorem and ordered descent prove finiteness;
no rank-zero hypothesis is supplied. -/
theorem finite_point_group : Finite W.Point := by
  apply FGKummer.finite_points_of_ordered_image (splitRoots 6 8)
    (splitRoots_injective 6 8 (by norm_num) (by norm_num) (by norm_num))
    (splitCurve_f_factorization 6 8) imageSet
  · exact mem_imageSet
  · exact imageSet_card

/-- The complete rational point list on A, obtained by descent and good
reduction, rather than a bounded search. -/
theorem complete_point_list (P : W.Point) :
    P=0 ∨ P=smallAZeroRoot ∨ P=smallASixRoot ∨ P=smallAEightRoot := by
  letI := finite_point_group
  exact small_A_point_list_of_card
    (SmallReduction.smallA_card_le_four_of_all_torsion (fun _ => isOfFinAddOrder_of_finite _)) P

theorem complete_affine_points {x y : ℚ} (h : y^2=x*(x-6)*(x-8)) :
    y=0 ∧ (x=0 ∨ x=6 ∨ x=8) := by
  letI := finite_point_group
  exact small_A_affine_points_of_card
    (SmallReduction.smallA_card_le_four_of_all_torsion (fun _ => isOfFinAddOrder_of_finite _)) h

theorem complete_affine_iff (x y : ℚ) :
    y^2=x*(x-6)*(x-8) ↔ y=0 ∧ (x=0 ∨ x=6 ∨ x=8) := by
  constructor
  · exact complete_affine_points
  · rintro ⟨rfl,rfl|rfl|rfl⟩ <;> norm_num

end
end FourCorner.NineSmallA
#print axioms FourCorner.NineSmallA.all_images
#print axioms FourCorner.NineSmallA.finite_point_group
#print axioms FourCorner.NineSmallA.complete_point_list
#print axioms FourCorner.NineSmallA.complete_affine_iff

namespace FourCorner.NineSmallA

/-- The auxiliary quartic has exactly its four rational branch points. -/
theorem complete_quartic_points {k v : ℚ}
    (h : v^2= -2*k*(k+2)*(1-k^2)) :
    v=0 ∧ (k=0 ∨ k= -2 ∨ k=1 ∨ k= -1) := by
  by_cases hk : k=0
  · subst k; norm_num at h; exact ⟨h,Or.inl rfl⟩
  have he : (-4*v/k^2)^2 = (4-4/k)*((4-4/k)-6)*((4-4/k)-8) := by
    field_simp
    nlinarith only [h]
  obtain ⟨hv,hx⟩ := complete_affine_points he
  have hv0 : v=0 := by
    have : -4*v=0 := (div_eq_zero_iff).mp hv |>.resolve_right (pow_ne_zero _ hk)
    linarith
  refine ⟨hv0,?_⟩
  rcases hx with hx|hx|hx
  · right; right; left
    field_simp at hx
    linarith
  · right; left
    field_simp at hx
    linarith
  · right; right; right
    field_simp at hx
    linarith

end FourCorner.NineSmallA
#print axioms FourCorner.NineSmallA.complete_quartic_points
