import Definitions.Def_AlgebraicCurve_AdelicIndex
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
set_option autoImplicit false
open AlgebraicCurve
namespace FourCorner.DivisorPicClassification
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

abbrev divisorClass (D : Divisor K F) : Pic K F := QuotientAddGroup.mk D

theorem class_eq_iff_principal_sub (D E : Divisor K F) :
    divisorClass D = divisorClass E ↔ (D-E).IsPrincipal :=
  QuotientAddGroup.eq_iff_sub_mem

/-- The function's actual all-place divisor, with its genuine degree-zero proof. -/
def principalDivisor [HasPrincipalDivisors K F] (f : F) (hf : f ≠ 0) : Divisor K F :=
  (HasPrincipalDivisors.exists_divisor f hf).choose

theorem principalDivisor_apply [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) (v : Place K F) :
    principalDivisor f hf v = v.ord f :=
  (HasPrincipalDivisors.exists_divisor f hf).choose_spec.1 v

theorem degree_principalDivisor [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    Divisor.degree (principalDivisor f hf : Divisor K F)=0 :=
  (HasPrincipalDivisors.exists_divisor f hf).choose_spec.2

theorem degree_eq_zero_of_principal [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D.IsPrincipal) : Divisor.degree D=0 := by
  obtain ⟨f,hf,hD⟩ := hD
  have he : D=principalDivisor f hf := by ext v; rw [hD v,principalDivisor_apply]
  rw [he,degree_principalDivisor]

def picDegree [HasPrincipalDivisors K F] : Pic K F →+ ℤ :=
  QuotientAddGroup.lift Divisor.principal Divisor.degree (by
    intro D hD
    exact degree_eq_zero_of_principal hD)

@[simp] theorem picDegree_class [HasPrincipalDivisors K F] (D : Divisor K F) :
    picDegree (divisorClass D)=Divisor.degree D := rfl

/-- Multiplication by the SAME actual function in the principal difference,
with the direction fixed by E-D=div(f). Zero vectors are handled explicitly. -/
def principalLSpaceEquiv {D E : Divisor K F} (f : F) (hf : f ≠ 0)
    (h : ∀v : Place K F,(E-D) v=v.ord f) : LSpace D ≃ₗ[K] LSpace E where
  toFun x := ⟨f⁻¹*x,by
    rcases mem_lSpace_iff_ord.mp x.2 with hx|hx
    · exact mem_lSpace_iff_ord.mpr (Or.inl (by rw [hx,mul_zero]))
    · by_cases h0 : (x:F)=0
      · exact mem_lSpace_iff_ord.mpr (Or.inl (by rw [h0,mul_zero]))
      · refine mem_lSpace_iff_ord.mpr (Or.inr fun v=>?_)
        rw [v.ord_mul (inv_ne_zero hf) h0,v.ord_inv]
        have hh:=h v
        simp only [Finsupp.sub_apply] at hh
        linarith [hx v]⟩
  invFun y := ⟨f*y,by
    rcases mem_lSpace_iff_ord.mp y.2 with hy|hy
    · exact mem_lSpace_iff_ord.mpr (Or.inl (by rw [hy,mul_zero]))
    · by_cases h0 : (y:F)=0
      · exact mem_lSpace_iff_ord.mpr (Or.inl (by rw [h0,mul_zero]))
      · refine mem_lSpace_iff_ord.mpr (Or.inr fun v=>?_)
        rw [v.ord_mul hf h0]
        have hh:=h v
        simp only [Finsupp.sub_apply] at hh
        linarith [hy v]⟩
  left_inv x := by ext; simp [←mul_assoc,hf]
  right_inv y := by ext; simp [←mul_assoc,hf]
  map_add' x y := by ext; exact mul_add _ _ _
  map_smul' a x := by ext; simp [Algebra.smul_def,mul_left_comm]

theorem ell_eq_of_principal_sub {D E : Divisor K F} (h : (E-D).IsPrincipal) :
    ell D=ell E := by
  obtain ⟨f,hf,h⟩ := h
  exact (principalLSpaceEquiv f hf h).finrank_eq

theorem ell_eq_of_class_eq {D E : Divisor K F} (h : divisorClass D=divisorClass E) :
    ell D=ell E :=
  ell_eq_of_principal_sub ((class_eq_iff_principal_sub E D).mp h.symm)

/-- Intrinsic h0 of a TRUE divisor Picard class, not a represented-Jacobian designation. -/
def picEll (c : Pic K F) : ℕ := ell c.out

@[simp] theorem picEll_class (D : Divisor K F) : picEll (divisorClass D)=ell D := by
  apply ell_eq_of_class_eq
  exact Quotient.out_eq _

 theorem ell_eq_picEll (D : Divisor K F) : ell D=picEll (divisorClass D) :=
  (picEll_class D).symm

#print axioms principalLSpaceEquiv
#print axioms ell_eq_of_class_eq
#print axioms picEll_class
end FourCorner.DivisorPicClassification
