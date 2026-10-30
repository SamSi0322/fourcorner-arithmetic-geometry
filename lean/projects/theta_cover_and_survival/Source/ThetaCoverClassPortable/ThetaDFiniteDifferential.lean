import ThetaCoverClassPortable.ThetaDActualDifferential
import ThetaCoverClassPortable.ThetaRegularFunctionDifferential

namespace FourCorner.ThetaDFiniteDifferential
open AlgebraicGeometry AlgebraicCurve MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDFieldCoordinates
open ThetaDActualDifferential ThetaDifferentialChartIdentity ThetaRegularFunctionDifferential
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem differential_relation :
    Fx x y • KaehlerDifferential.D K field x+
      Fy x y • KaehlerDifferential.D K field y=0 := by
  have hc (n:ℕ) [n.AtLeastTwo] : KaehlerDifferential.D K field (OfNat.ofNat n)=0 :=
    (KaehlerDifferential.D K field).map_natCast n
  have h := congrArg (KaehlerDifferential.D K field) polynomial_relation
  simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
    hc,map_zero] at h
  unfold Fx Fy
  convert h using 1 <;> module

 theorem omega_eq_neg_dy (hx : Fx x y ≠ 0) :
    omega=(-(Fx x y)⁻¹) • KaehlerDifferential.D K field y := by
  have h := differential_relation
  have he : Fx x y • KaehlerDifferential.D K field x=
      -(Fy x y • KaehlerDifferential.D K field y) := eq_neg_of_add_eq_zero_left h
  have hd : KaehlerDifferential.D K field x=
      ((Fx x y)⁻¹ * -(Fy x y)) • KaehlerDifferential.D K field y := by
    have hh := congrArg (fun z : Ω[field⁄K] => (Fx x y)⁻¹ • z) he
    simpa only [smul_smul,inv_mul_cancel₀ hx,one_smul,smul_neg,neg_smul,mul_neg] using hh
  rw [omega,hd,smul_smul]
  congr 1
  field_simp [Fy_ne_zero]

/-- Smoothness of the SAME literal quartic, expressed at arbitrary field
values, using the already proved actual chart Jacobian certificate. -/
theorem gradient_nonzero {E : Type} [Field E] [CharZero E] [Algebra ℚ E]
    (a b : E)
    (h : 9801*a^4+19598*a^2*b^2-39592*a^2+9801*b^4-39592*b^2+39984=0) :
    Fx a b ≠ 0 ∨ Fy a b ≠ 0 := by
  have hv : ∀i : Fin 1,MvPolynomial.aeval ![a,b]
      (ThetaQuotientChart.affineEquation (targetEquation ℚ) 2 i)=0 := by
    intro i;fin_cases i
    norm_num [ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
      targetEquation,targetPolynomial,ThetaTargetSmooth.drop_table,Fin.isValue]
    simp
    linear_combination h
  let f : ThetaTargetSmooth.ar (k:=ℚ) 2 →ₐ[ℚ] E :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![a,b]) (by
      have hi : ThetaQuotientChart.affineIdeal (targetEquation ℚ) 2 ≤
          RingHom.ker (MvPolynomial.aeval ![a,b]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩;exact hv i
      exact fun z hz=>hi hz)
  obtain ⟨i,hi⟩ := ThetaTargetSmooth.field_jacobian (k:=ℚ) 2 E f
  rw [ThetaTargetSmooth.jacobian_formula] at hi
  have he (j : Fin 2) : f (ThetaTargetSmooth.ax 2 j)=![a,b] j := MvPolynomial.aeval_X _ _
  simp only [he] at hi
  fin_cases i
  · left;convert hi using 1 <;> simp [ThetaTargetSmooth.minorScalar,Fx] <;> ring
  · right;convert hi using 1 <;> simp [ThetaTargetSmooth.minorScalar,Fy] <;> ring

 theorem inv_mem_of_isUnit {A : ValuationSubring field} {a : A} (ha : IsUnit a) :
    (a:field)⁻¹ ∈ A := by
  rcases ha with ⟨u,rfl⟩
  have hm : (((u⁻¹ : Aˣ):A):field)*((u:A):field)=1 := by
    exact congrArg (fun z : A => (z:field)) u.inv_val
  have hh : (((u⁻¹ : Aˣ):A):field)=(((u:A):field))⁻¹ :=
    eq_inv_of_mul_eq_one_left hm
  rw [←hh]
  exact ((u⁻¹:Aˣ):A).property

/-- At EVERY actual place where the true affine coordinates are regular,
one of the two genuine partial derivatives is a local unit. -/
theorem partial_unit (w : Place K field) (hx : x∈w.toValuationSubring)
    (hy : y∈w.toValuationSubring) :
    (Fx x y ≠ 0 ∧ (Fx x y)⁻¹∈w.toValuationSubring) ∨
      (Fy x y ≠ 0 ∧ (Fy x y)⁻¹∈w.toValuationSubring) := by
  let A := w.toValuationSubring
  let a : A := ⟨x,hx⟩
  let b : A := ⟨y,hy⟩
  have he : 9801*a^4+19598*a^2*b^2-39592*a^2+9801*b^4-39592*b^2+39984=0 := by
    apply Subtype.val_injective
    exact polynomial_relation
  let r := IsLocalRing.residue A
  have hr := congrArg r he
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero] at hr
  letI : CharZero w.ResidueField := charZero_of_injective_algebraMap (algebraMap K w.ResidueField).injective
  letI : Algebra ℚ w.ResidueField := ((algebraMap K w.ResidueField).comp (algebraMap ℚ K)).toAlgebra
  rcases gradient_nonzero (r a) (r b) hr with hf | hf
  · left
    let fx : A := a*(39204*a^2+39196*b^2-79184)
    have hh : IsUnit fx := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by
      simpa only [fx,Fx,map_mul,map_add,map_sub,map_pow,map_ofNat] using hf)
    exact ⟨fun hz => hh.ne_zero (Subtype.ext hz),inv_mem_of_isUnit hh⟩
  · right
    let fy : A := b*(39196*a^2+39204*b^2-79184)
    have hh : IsUnit fy := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by
      simpa only [fy,Fy,map_mul,map_add,map_sub,map_pow,map_ofNat] using hf)
    exact ⟨fun hz => hh.ne_zero (Subtype.ext hz),inv_mem_of_isUnit hh⟩

 theorem omega_regular_where_coordinates_regular (w : Place K field)
    (hx : x∈w.toValuationSubring) (hy : y∈w.toValuationSubring) :
    coefficient w omega∈w.toValuationSubring := by
  rcases partial_unit w hx hy with ⟨hfx,hf⟩ | ⟨_,hf⟩
  · rw [omega_eq_neg_dy hfx,map_smul]
    exact w.toValuationSubring.toSubring.mul_mem (w.toValuationSubring.toSubring.neg_mem hf)
      (coefficient_D_mem w y hy)
  · change coefficient w ((Fy x y)⁻¹ • KaehlerDifferential.D K field x)∈_
    rw [map_smul]
    exact w.toValuationSubring.toSubring.mul_mem hf (coefficient_D_mem w x hx)

#print axioms differential_relation
#print axioms gradient_nonzero
#print axioms partial_unit
#print axioms omega_regular_where_coordinates_regular
end
end FourCorner.ThetaDFiniteDifferential
