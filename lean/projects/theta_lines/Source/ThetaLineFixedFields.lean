import ThetaOrbitEvaluation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra

def fixedBy (σ : G) : Subalgebra ℚ K where
  carrier := {z | σ z = z}
  algebraMap_mem' q := σ.commutes q
  zero_mem' := map_zero σ
  one_mem' := map_one σ
  add_mem' {a b} hz hw := by
    change σ (a + b) = a + b
    change σ a = a at hz
    change σ b = b at hw
    rw [map_add, hz, hw]
  mul_mem' {a b} hz hw := by
    change σ (a * b) = a * b
    change σ a = a at hz
    change σ b = b at hw
    rw [map_mul, hz, hw]

def fixedTwo : Subalgebra ℚ K := fixedBy thetaFlipFiftyone
def fixedFiftyone : Subalgebra ℚ K := fixedBy thetaFlipTwo
def fixedRational : Subalgebra ℚ K := fixedTwo ⊓ fixedFiftyone

private theorem zero_of_neg_eq {F : Type*} [Field F] [CharZero F] (z : F) (h : -z = z) : z = 0 := by
  have hh : (2 : F) * z = 0 := by
    calc
      2 * z = z + z := by ring
      _ = -z + z := congrArg (fun w => w + z) h.symm
      _ = 0 := neg_add_cancel z
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

private theorem fixedTwo_im (z : fixedTwo) : (z : K).im = 0 := by
  apply zero_of_neg_eq
  exact congrArg QuadraticAlgebra.im z.2
private theorem fixedFiftyone_re_im (z : fixedFiftyone) : (z : K).re.im = 0 := by
  apply zero_of_neg_eq
  exact congrArg (fun z : K => z.re.im) z.2
private theorem fixedFiftyone_im_im (z : fixedFiftyone) : (z : K).im.im = 0 := by
  apply zero_of_neg_eq
  exact congrArg (fun z : K => z.im.im) z.2

/-- The genuine Q(sqrt(2)) is exactly the fixed subalgebra of the s-sign change. -/
def sqrtTwoFixedEquiv : ThetaSqrtTwo ≃ₐ[ℚ] fixedTwo := by
  let e : ThetaSqrtTwo →ₐ[ℚ] fixedTwo :=
    (IsScalarTower.toAlgHom ℚ ThetaSqrtTwo K).codRestrict fixedTwo (fun z => by
      change thetaFlipFiftyone (algebraMap ThetaSqrtTwo K z) = _
      apply QuadraticAlgebra.ext <;> rfl)
  refine AlgEquiv.ofBijective e ⟨?_, ?_⟩
  · intro x y h
    exact (algebraMap ThetaSqrtTwo K).injective (congrArg Subtype.val h)
  · intro z
    refine ⟨(z : K).re, Subtype.ext ?_⟩
    change (algebraMap ThetaSqrtTwo K (z : K).re) = (z : K)
    exact QuadraticAlgebra.ext rfl (fixedTwo_im z).symm

/-- An actual model of Q(sqrt(51)), with nonsquareness supplying the FIELD instance. -/
abbrev SqrtFiftyone := QuadraticAlgebra ℚ 51 0
instance fiftyoneIrreducible : Fact (∀ q : ℚ, q ^ 2 ≠ 51 + 0 * q) :=
  ⟨fun q => by simpa using theta_rat_sq_ne_fiftyone q⟩

instance fiftyoneFinite : FiniteDimensional ℚ SqrtFiftyone := inferInstance

theorem fiftyone_degree : Module.finrank ℚ SqrtFiftyone = 2 := QuadraticAlgebra.finrank_eq_two 51 0

theorem sqrtTwo_degree : Module.finrank ℚ ThetaSqrtTwo = 2 := QuadraticAlgebra.finrank_eq_two 2 0

theorem sqrtTwo_generator_absolute :
    ThetaLinesAbsoluteGalois.splittingEmbedding
      (algebraMap ThetaSqrtTwo K (QuadraticAlgebra.omega : ThetaSqrtTwo)) =
      ThetaLinesAbsoluteGalois.r := rfl

def fiftyoneEmbedding : SqrtFiftyone →ₐ[ℚ] K := QuadraticAlgebra.lift
  ⟨thetaGaloisS, by
    rw [← pow_two, thetaGaloisS_sq]
    norm_num [Algebra.smul_def]⟩

@[simp] theorem fiftyoneEmbedding_generator :
    fiftyoneEmbedding (QuadraticAlgebra.omega : SqrtFiftyone) = thetaGaloisS := by
  change (0 : ℚ) • (1 : K) + (1 : ℚ) • thetaGaloisS = thetaGaloisS
  simp

theorem fiftyone_generator_absolute :
    ThetaLinesAbsoluteGalois.splittingEmbedding
      (fiftyoneEmbedding (QuadraticAlgebra.omega : SqrtFiftyone)) =
      ThetaLinesAbsoluteGalois.s := by rw [fiftyoneEmbedding_generator]; rfl

theorem fiftyoneEmbedding_eq (z : SqrtFiftyone) :
    fiftyoneEmbedding z = (⟨⟨z.re, 0⟩, ⟨z.im, 0⟩⟩ : K) := by
  ext <;> simp [fiftyoneEmbedding, QuadraticAlgebra.lift, thetaGaloisS, QuadraticAlgebra.omega]

/-- The genuine Q(sqrt(51)) is exactly the fixed subalgebra of the r-sign change. -/
def sqrtFiftyoneFixedEquiv : SqrtFiftyone ≃ₐ[ℚ] fixedFiftyone := by
  let e : SqrtFiftyone →ₐ[ℚ] fixedFiftyone := fiftyoneEmbedding.codRestrict fixedFiftyone (fun z => by
    change thetaFlipTwo (fiftyoneEmbedding z) = fiftyoneEmbedding z
    rw [fiftyoneEmbedding_eq]
    ext <;> simp [thetaFlipTwo])
  refine AlgEquiv.ofBijective e ⟨?_, ?_⟩
  · intro x y h
    exact fiftyoneEmbedding.injective (congrArg Subtype.val h)
  · intro z
    refine ⟨⟨(z : K).re.re, (z : K).im.re⟩, Subtype.ext ?_⟩
    change fiftyoneEmbedding _ = (z : K)
    rw [fiftyoneEmbedding_eq]
    exact QuadraticAlgebra.ext
      (QuadraticAlgebra.ext rfl (fixedFiftyone_re_im z).symm)
      (QuadraticAlgebra.ext rfl (fixedFiftyone_im_im z).symm)

/-- The intersection of the two actual sign fixed subalgebras is the ACTUAL rational image. -/
def rationalFixedEquiv : ℚ ≃ₐ[ℚ] fixedRational := by
  let e : ℚ →ₐ[ℚ] fixedRational := (Algebra.ofId ℚ K).codRestrict fixedRational
    (fun q => ⟨thetaFlipFiftyone.commutes q, thetaFlipTwo.commutes q⟩)
  refine AlgEquiv.ofBijective e ⟨?_, ?_⟩
  · intro x y h
    exact (algebraMap ℚ K).injective (congrArg Subtype.val h)
  · intro z
    have hzS : (z : K).im = 0 := fixedTwo_im ⟨z, z.2.1⟩
    have hzR : (z : K).re.im = 0 := fixedFiftyone_re_im ⟨z, z.2.2⟩
    refine ⟨(z : K).re.re, Subtype.ext ?_⟩
    change algebraMap ℚ K (z : K).re.re = (z : K)
    exact QuadraticAlgebra.ext (QuadraticAlgebra.ext rfl hzR.symm) hzS.symm
end FourCorner.ThetaLineGaloisAlgebra
