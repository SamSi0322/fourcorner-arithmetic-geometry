import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import CommonBoundaryCharts
import CommonLiteralField

noncomputable section
namespace FourCorner.CommonRationalPlace
open AlgebraicCurve
variable {F : Type*} [Field F] [Algebra ℚ F]

/-- The actual residue homomorphism of a rational place, with residue field
identified with Q by the inverse of its constant-field embedding. -/
def rationalEval (w : Place ℚ F) (hw : w.IsRational) :
    w.toValuationSubring →ₐ[ℚ] ℚ :=
  (AlgEquiv.ofBijective (Algebra.ofId ℚ w.ResidueField)
    ⟨(algebraMap ℚ w.ResidueField).injective, hw⟩).symm.toAlgHom.comp
      (IsScalarTower.toAlgHom ℚ w.toValuationSubring w.ResidueField)

/-- Square roots of regular functions are regular at the same actual place. -/
theorem root_mem (w : Place ℚ F) {a r : F} (ha : a ∈ w.toValuationSubring)
    (hr : r^2 = a) : r ∈ w.toValuationSubring := by
  have hi : IsIntegral w.toValuationSubring r := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hr]
    exact isIntegral_algebraMap (x := (⟨a,ha⟩ : w.toValuationSubring))
  obtain ⟨y,hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact hy ▸ y.property

/-- A regular function with nonzero rational residue is a unit in the
actual valuation ring; hence its field inverse is regular there. -/
theorem inv_mem_of_eval_ne_zero (w : Place ℚ F) (hw : w.IsRational)
    (e : w.toValuationSubring) (he : rationalEval w hw e ≠ 0) :
    (e:F)⁻¹ ∈ w.toValuationSubring := by
  have hres : IsLocalRing.residue w.toValuationSubring e ≠ 0 := by
    intro hz
    apply he
    change (AlgEquiv.ofBijective (Algebra.ofId ℚ w.ResidueField)
      ⟨(algebraMap ℚ w.ResidueField).injective, hw⟩).symm
        (IsLocalRing.residue w.toValuationSubring e) = 0
    rw [hz, map_zero]
  have heunit : IsUnit e := (IsLocalRing.residue_ne_zero_iff_isUnit e).mp hres
  obtain ⟨y,hy⟩ := heunit.exists_left_inv
  have hyF : (y:F) * (e:F) = 1 := congrArg (fun x : w.toValuationSubring => (x:F)) hy
  have heF : (e:F) ≠ 0 := by intro hh; rw [hh,mul_zero] at hyF; exact zero_ne_one hyF
  have hyinv : (y:F) = (e:F)⁻¹ := by apply (mul_right_cancel₀ heF); rw [hyF,inv_mul_cancel₀ heF]
  exact hyinv ▸ y.property

/-- A genuine rational place cannot be a pole of ell. This retains every
place over infinity: the reciprocal coordinate is regular there and has
zero residue; the M equation forces the negative square -(t-1). -/
theorem ell_mem_of_rational (w : Place ℚ F) (hw : w.IsRational)
    (t : ℚ) (ht : 1 < t) (e M : F) (he0 : e ≠ 0)
    (hM : M^2 = algebraMap ℚ F (t-1)*(algebraMap ℚ F (t+1)-e)/e) :
    e ∈ w.toValuationSubring := by
  by_contra hnot
  let A := w.toValuationSubring
  have hinv : e⁻¹ ∈ A := (A.mem_or_inv_mem e).resolve_left hnot
  let Z : A := ⟨e⁻¹,hinv⟩
  let f := rationalEval w hw
  have hz : f Z = 0 := by
    by_contra hz
    have h := inv_mem_of_eval_ne_zero w hw Z hz
    apply hnot
    simpa only [Z, inv_inv] using h
  have hMr : M^2 = algebraMap ℚ F (t-1)*
      (algebraMap ℚ F (t+1)*e⁻¹-1) := by
    rw [hM]
    field_simp
  have hMm : M ∈ A := root_mem w
    (A.mul_mem _ _ (w.algebraMap_mem' _)
      (A.sub_mem (A.mul_mem _ _ (w.algebraMap_mem' _) hinv) A.one_mem)) hMr
  let MM : A := ⟨M,hMm⟩
  have hMM : MM^2 = algebraMap ℚ A (t-1)*(algebraMap ℚ A (t+1)*Z-1) := by
    apply Subtype.ext
    exact hMr
  exact CommonBoundaryCharts.no_eval_at_infinity t ht f Z MM hMM hz

/-- All five finite omitted fibres are excluded for genuine rational
places of any field carrying the literal four-root equations. The selected
regular roots are derived from integrality; roots are never assumed nonzero. -/
theorem finite_boundary_excluded (w : Place ℚ F) (hw : w.IsRational)
    (t : ℚ) (ht : 1 < t) (e P C M B : F) (he0 : e ≠ 0)
    (hP : P^2 = e + algebraMap ℚ F (t+1))
    (hC : C^2 = e - algebraMap ℚ F (t-1))
    (hM : M^2 = algebraMap ℚ F (t-1)*(algebraMap ℚ F (t+1)-e)/e)
    (hB : B^2 = algebraMap ℚ F (t+1)*(e+algebraMap ℚ F (t-1))/e)
    (he : e ∈ w.toValuationSubring) :
    rationalEval w hw ⟨e,he⟩ ∉ ({0,t-1,t+1,-(t-1),-(t+1)} : Finset ℚ) := by
  let A := w.toValuationSubring
  let E : A := ⟨e,he⟩
  let f := rationalEval w hw
  have hPm : P ∈ A := root_mem w
    (A.add_mem _ _ he (w.algebraMap_mem' (t+1))) hP
  have hCm : C ∈ A := root_mem w
    (A.sub_mem he (w.algebraMap_mem' (t-1))) hC
  let PP : A := ⟨P,hPm⟩
  let CC : A := ⟨C,hCm⟩
  have hPP : PP^2 = E + algebraMap ℚ A (t+1) := by apply Subtype.ext; exact hP
  have hCC : CC^2 = E - algebraMap ℚ A (t-1) := by apply Subtype.ext; exact hC
  intro hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hb | hb | hb | hb | hb
  · exact CommonBoundaryCharts.no_eval_at_zero t ht f E CC hCC hb
  · have hinv := inv_mem_of_eval_ne_zero w hw E (by dsimp [f,E]; rw [hb]; linarith)
    have hMm : M ∈ A := root_mem w
      (by change algebraMap ℚ F (t-1)*(algebraMap ℚ F (t+1)-e)/e ∈ A
          simpa only [div_eq_mul_inv] using A.mul_mem _ _ (A.mul_mem _ _ (w.algebraMap_mem' (t-1)) (A.sub_mem (w.algebraMap_mem' (t+1)) he)) hinv) hM
    let MM : A := ⟨M,hMm⟩
    have hMM : E*MM^2 = algebraMap ℚ A (t-1)*(algebraMap ℚ A (t+1)-E) := by
      apply Subtype.ext
      change e*M^2 = algebraMap ℚ F (t-1)*(algebraMap ℚ F (t+1)-e)
      rw [hM]
      field_simp
      all_goals assumption
    exact CommonBoundaryCharts.no_eval_at_s t (by linarith) f E MM hMM hb
  · exact CommonBoundaryCharts.no_eval_at_T t f E CC hCC hb
  · exact CommonBoundaryCharts.no_eval_at_neg_s t f E PP hPP hb
  · have hinv := inv_mem_of_eval_ne_zero w hw E (by dsimp [f,E]; rw [hb]; linarith)
    have hBm : B ∈ A := root_mem w
      (by change algebraMap ℚ F (t+1)*(e+algebraMap ℚ F (t-1))/e ∈ A
          simpa only [div_eq_mul_inv] using A.mul_mem _ _ (A.mul_mem _ _ (w.algebraMap_mem' (t+1)) (A.add_mem _ _ he (w.algebraMap_mem' (t-1)))) hinv) hB
    let BB : A := ⟨B,hBm⟩
    have hBB : E*BB^2 = algebraMap ℚ A (t+1)*(E+algebraMap ℚ A (t-1)) := by
      apply Subtype.ext
      change e*B^2 = algebraMap ℚ F (t+1)*(e+algebraMap ℚ F (t-1))
      rw [hB]
      field_simp
      all_goals assumption
    exact CommonBoundaryCharts.no_eval_at_neg_T t (by linarith) f E BB hBB hb

#print axioms ell_mem_of_rational
#print axioms finite_boundary_excluded
#print axioms inv_mem_of_eval_ne_zero
#print axioms rationalEval
#print axioms root_mem
end FourCorner.CommonRationalPlace
