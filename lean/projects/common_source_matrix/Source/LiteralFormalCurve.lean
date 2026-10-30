import DerivationPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision

abbrev FormalFrac (K : Type*) [Field K] := FractionRing (PowerSeries K)
variable {K : Type*} [Field K]

instance formalFrac_charZero [CharZero K] : CharZero (FormalFrac K) :=
  charZero_of_injective_algebraMap (algebraMap K (FormalFrac K)).injective

def formalMap : PowerSeries K →+* FormalFrac K := algebraMap _ _
def formalZ : FormalFrac K := formalMap PowerSeries.X
def formalV (W : WeierstrassCurve K) : FormalFrac K := formalMap W.vSeries
def formalW (W : WeierstrassCurve K) : FormalFrac K := formalMap W.wSeries
def formalX (W : WeierstrassCurve K) : FormalFrac K := formalZ/formalW W
def formalY (W : WeierstrassCurve K) : FormalFrac K := -1/formalW W

lemma formalMap_injective : Function.Injective (formalMap (K:=K)) :=
  IsFractionRing.injective (PowerSeries K) (FormalFrac K)

lemma formalMap_ne_zero {f : PowerSeries K} (hf : f ≠ 0) : formalMap f ≠ 0 := by
  intro h
  apply hf
  apply formalMap_injective
  simpa only [map_zero] using h

lemma formalMap_C (a : K) : formalMap (PowerSeries.C a)=algebraMap K (FormalFrac K) a := by
  change algebraMap (PowerSeries K) (FormalFrac K) (algebraMap K (PowerSeries K) a)=_
  exact (IsScalarTower.algebraMap_apply K (PowerSeries K) (FormalFrac K) a).symm

lemma formalZ_ne_zero : (formalZ:FormalFrac K) ≠ 0 :=
  formalMap_ne_zero (PowerSeries.X_ne_zero (R:=K))

lemma formalV_ne_zero (W : WeierstrassCurve K) : formalV W ≠ 0 := by
  apply formalMap_ne_zero
  intro h
  have hc := W.constantCoeff_vSeries
  rw [h,map_zero] at hc
  exact zero_ne_one hc

lemma formalW_factor (W : WeierstrassCurve K) : formalW W=formalZ^3*formalV W := by
  unfold formalW
  rw [W.wSeries_eq_X_pow_three_mul,map_mul,map_pow]
  rfl

lemma formalW_ne_zero (W : WeierstrassCurve K) : formalW W ≠ 0 := by
  rw [formalW_factor]
  exact mul_ne_zero (pow_ne_zero _ formalZ_ne_zero) (formalV_ne_zero W)

lemma formalY_ne_zero (W : WeierstrassCurve K) : formalY W ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr one_ne_zero) (formalW_ne_zero W)

lemma formal_two_sub_v_ne_zero (W : WeierstrassCurve K) : 2-formalV W ≠ 0 := by
  have h := formalMap_ne_zero (two_sub_v_ne_zero W)
  simpa only [formalV,map_sub,map_ofNat] using h

lemma formalV_relation (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    formalV W=1+algebraMap K (FormalFrac K) W.a₄*formalZ^4*(formalV W)^2 := by
  have h := congrArg (formalMap (K:=K)) (short_v_equation W h1 h2 h3 h6)
  simpa only [formalV,formalZ,map_add,map_one,map_mul,map_pow,formalMap_C] using h

lemma formal_omega_value (W : WeierstrassCurve K) :
    formalMap (shortOmega W)=formalV W/(2-formalV W) := by
  have h := congrArg (formalMap (K:=K)) (two_sub_v_mul_omega W)
  simp only [map_mul,map_sub,map_ofNat] at h
  apply (eq_div_iff (formal_two_sub_v_ne_zero W)).mpr
  change formalMap (shortOmega W)*(2-formalMap W.vSeries)=formalMap W.vSeries
  rw [mul_comm]
  exact h

lemma formal_w_equation (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    formalW W=formalZ^3+algebraMap K (FormalFrac K) W.a₄*formalZ*(formalW W)^2 := by
  have h := W.wSeries_eq
  simp only [h1,h2,h3,h6,map_zero,zero_mul,mul_zero,add_zero,zero_add] at h
  have hh := congrArg (formalMap (K:=K)) h
  simpa only [formalW,formalZ,map_add,map_mul,map_pow,formalMap_C] using hh

/-- The actual formal field coordinates satisfy the original curve equation. -/
theorem formal_coordinates_cubic (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (formalY W)^2=(formalX W)^3+algebraMap K (FormalFrac K) W.a₄*formalX W := by
  have hw := formalW_ne_zero W
  have he := formal_w_equation W h1 h2 h3 h6
  unfold formalX formalY
  calc
    (-1/formalW W)^2=1/(formalW W)^2 := by ring
    _=(formalZ^3+algebraMap K (FormalFrac K) W.a₄*formalZ*(formalW W)^2)/(formalW W)^3 := by
      rw [← he]
      field_simp
    _=(formalZ/formalW W)^3+algebraMap K (FormalFrac K) W.a₄*(formalZ/formalW W) := by
      field_simp <;> ring

theorem formal_coordinates_equation (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (W.map (algebraMap K (FormalFrac K))).toAffine.Equation (formalX W) (formalY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa only [WeierstrassCurve.map,WeierstrassCurve.toAffine,h1,h2,h3,h6,
    map_zero,zero_mul,mul_zero,add_zero,zero_add] using formal_coordinates_cubic W h1 h2 h3 h6

theorem formal_coordinates_nonsingular [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (W.map (algebraMap K (FormalFrac K))).toAffine.Nonsingular (formalX W) (formalY W) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  refine ⟨formal_coordinates_equation W h1 h2 h3 h6,Or.inr ?_⟩
  simpa only [WeierstrassCurve.map,WeierstrassCurve.toAffine,h1,h3,map_zero,zero_mul,add_zero] using
    mul_ne_zero (by norm_num : (2:FormalFrac K) ≠ 0) (formalY_ne_zero W)

/-- A genuine nonsingular point of the original curve over its formal fraction
field, retaining both literal coordinates. -/
def formalCurvePoint [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (W.map (algebraMap K (FormalFrac K))).toAffine.Point :=
  .some (formalX W) (formalY W) (formal_coordinates_nonsingular W h1 h2 h3 h6)

theorem formal_coordinate_parameter (W : WeierstrassCurve K) :
    -formalX W/formalY W=(formalZ:FormalFrac K) := by
  unfold formalX formalY
  field_simp [formalW_ne_zero W]

/-- Literal geometric dx/(2y) in the native universal differential module of
the actual formal field. No universal differential of the transcendental log
is equated with its continuous/formal derivative. -/
theorem literal_differential_pullback [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (2*formalY W)⁻¹ • (KaehlerDifferential.D K (FormalFrac K)) (formalX W)=
      formalMap (shortOmega W) • (KaehlerDifferential.D K (FormalFrac K)) (formalZ:FormalFrac K) := by
  rw [formal_omega_value]
  unfold formalX formalY
  rw [formalW_factor]
  exact derivation_dx_over_two_y (KaehlerDifferential.D K (FormalFrac K))
    ((KaehlerDifferential.D K (FormalFrac K)).map_algebraMap W.a₄)
    (formalV_relation W h1 h2 h3 h6) formalZ_ne_zero (formalV_ne_zero W)
    (formal_two_sub_v_ne_zero W) (by norm_num)

#print axioms formalCurvePoint
#print axioms formal_coordinate_parameter
#print axioms literal_differential_pullback
end FourCorner.CommonSource.LogPrecision
