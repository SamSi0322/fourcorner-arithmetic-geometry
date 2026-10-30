import HpBranchLinearDescent
import HasseOrderedBranchBridge
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace FourCorner.HpNativeBranchEquivalence
open HpLiteralField HpFieldGeometry HpQuadraticRelations HpBranchLinearDescent
  ProjectiveThreePoint HasseBranchConfiguration HasseOrderedBranchBridge
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix
variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]

def branchVector (p : K) (i : Fin 5) : ProjectiveThreePoint.V K := ![-intercept K p i,slope K p i]

theorem branchVector_ne_zero (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 5) :
    branchVector K p i ≠ 0 := by
  intro h
  have ht := congrFun h 0
  have hs := congrFun h 1
  have hi : intercept K p i=0 := by simpa [branchVector] using ht
  have hi' : slope K p i=0 := by simpa [branchVector] using hs
  obtain ⟨j,hj⟩ := exists_ne i
  apply HpAxisQuadrics.determinant_ne_zero K p hp ha hb i j (Ne.symm hj)
  simp [HpAxisQuadrics.determinant,hi,hi']

def point (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 5) : Line K :=
  Projectivization.mk K (branchVector K p i) (branchVector_ne_zero K p hp ha hb i)

theorem point_eq_ordered (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 5) :
    point K p hp ha hb i=ordered (by norm_num) p i := by
  fin_cases i
  · apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨p,?_⟩
    ext j;fin_cases j <;> simp [branchVector,slope,intercept,ProjectiveThreePoint.e1]
  · apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨2*(p-1),?_⟩
    ext j;fin_cases j <;> simp [branchVector,slope,intercept,ProjectiveThreePoint.e0,ProjectiveThreePoint.e1]
  · apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨2*(p+1),?_⟩
    ext j;fin_cases j <;> simp [branchVector,slope,intercept]
  · apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨1,?_⟩
    simp [branchVector,slope,intercept,parameterVector]
  · apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨-1,?_⟩
    ext j;fin_cases j <;> simp [branchVector,slope,intercept,ProjectiveThreePoint.e0]

/-- An actual K-field isomorphism induces genuine projective equivalence
of all five literal branch points, with no chosen marking. -/
theorem equivalent_of_field_iso {p q : K} (e : field K p ≃ₐ[K] field K q)
    (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hq : q ≠ 0) (hqa : q-1 ≠ 0) (hqb : q+1 ≠ 0) :
    Equivalent (by norm_num) p q := by
  obtain ⟨σ,B,b,hd,hn,hcov⟩ := actual_branch_matrix K e hp ha hb hq hqa hqb
  have had : IsUnit B.adjugate.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_adjugate]
    simpa using hd
  letI : Invertible B.adjugate := Matrix.invertibleOfIsUnitDet B.adjugate had
  let g : ProjectiveThreePoint.V K ≃ₗ[K] ProjectiveThreePoint.V K := B.adjugate.toLinearEquiv' inferInstance
  have hg (i : Fin 5) : g (branchVector K p i)=b i • branchVector K q (σ i) := by
    change (B.adjugate *ᵥ branchVector K p i)=_
    obtain ⟨h0,h1⟩ := hcov i
    ext j
    fin_cases j
    · simp [Matrix.adjugate_fin_two,Matrix.mulVec,dotProduct,Fin.sum_univ_two,branchVector]
      linear_combination -h1
    · simp [Matrix.adjugate_fin_two,Matrix.mulVec,dotProduct,Fin.sum_univ_two,branchVector]
      linear_combination h0
  apply equivalent_of_ordered_perm (by norm_num) p q g σ
  intro i
  rw [← point_eq_ordered K p hp ha hb,← point_eq_ordered K q hq hqa hqb]
  change Projectivization.mk K (g (branchVector K p i)) _=Projectivization.mk K (branchVector K q (σ i)) _
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  exact ⟨b i,(hg i).symm⟩

#print axioms point_eq_ordered
#print axioms equivalent_of_field_iso
end
end FourCorner.HpNativeBranchEquivalence
