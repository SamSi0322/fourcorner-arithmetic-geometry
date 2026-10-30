import ThetaCoverClassPortable.LaurentPresentationMaps
import Mathlib.RingTheory.Polynomial.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial LaurentPolynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R] {ι : Type*} [Fintype ι]
  {S : TwoChartCech.Sections (laurentCover R)} {d : ℤ}
namespace LaurentPresentation
variable (p : LaurentPresentation S d ι)

/- Actual polynomial/Laurent kernels of the three presentation maps form
the actual kernel gluing datum. Restriction squares prove membership. -/
set_option maxHeartbeats 800000 in
def kernelSections : TwoChartCech.Sections (laurentCover R) := by
  letI : Module R[X] (LinearMap.ker p.negative) := inferInstance
  letI : Module R[X] (LinearMap.ker p.positive) := inferInstance
  letI : Module (LaurentPolynomial R) (LinearMap.ker p.overlap) := inferInstance
  letI : Module R (LinearMap.ker p.negative) := inferInstance
  letI : Module R (LinearMap.ker p.positive) := inferInstance
  letI : Module R (LinearMap.ker p.overlap) := inferInstance
  haveI : IsScalarTower R R[X] (LinearMap.ker p.negative) := inferInstance
  haveI : IsScalarTower R R[X] (LinearMap.ker p.positive) := inferInstance
  haveI : IsScalarTower R (LaurentPolynomial R) (LinearMap.ker p.overlap) := inferInstance
  exact {
  M0 := LinearMap.ker p.negative
  M1 := LinearMap.ker p.positive
  M01 := LinearMap.ker p.overlap
  M0_moduleA := inferInstanceAs (Module R[X] (LinearMap.ker p.negative))
  M1_moduleA := inferInstanceAs (Module R[X] (LinearMap.ker p.positive))
  M01_moduleA := inferInstanceAs (Module (LaurentPolynomial R) (LinearMap.ker p.overlap))
  M0_module := inferInstanceAs (Module R (LinearMap.ker p.negative))
  M1_module := inferInstanceAs (Module R (LinearMap.ker p.positive))
  M01_module := inferInstanceAs (Module R (LinearMap.ker p.overlap))
  M0_tower := by infer_instance
  M1_tower := by infer_instance
  M01_tower := by infer_instance
  r0 := {
    toFun := fun x => ⟨(freeTwistSections (R := R) (ι := ι) d).r0 x.val,by
      rw [LinearMap.mem_ker,←p.comm_negative]
      rw [x.property,map_zero]⟩
    map_add' := fun x y => Subtype.ext ((freeTwistSections (R := R) (ι := ι) d).r0.map_add _ _)
    map_smul' := fun a x => by
      apply Subtype.ext
      exact (freeTwistSections (R := R) (ι := ι) d).r0.map_smul a x.val }
  r1 := {
    toFun := fun x => ⟨(freeTwistSections (R := R) (ι := ι) d).r1 x.val,by
      rw [LinearMap.mem_ker,←p.comm_positive]
      rw [x.property,map_zero]⟩
    map_add' := fun x y => Subtype.ext ((freeTwistSections (R := R) (ι := ι) d).r1.map_add _ _)
    map_smul' := fun a x => by
      apply Subtype.ext
      exact (freeTwistSections (R := R) (ι := ι) d).r1.map_smul a x.val }
  r0_smul := by
    intro a x
    apply Subtype.ext
    change (freeTwistSections (R := R) (ι := ι) d).r0 (a • x.val) =
      (laurentCover R).ρ0 a • (freeTwistSections (R := R) (ι := ι) d).r0 x.val
    exact (freeTwistSections (R := R) (ι := ι) d).r0_smul a x.val
  r1_smul := by
    intro a x
    apply Subtype.ext
    change (freeTwistSections (R := R) (ι := ι) d).r1 (a • x.val) =
      (laurentCover R).ρ1 a • (freeTwistSections (R := R) (ι := ι) d).r1 x.val
    exact (freeTwistSections (R := R) (ι := ι) d).r1_smul a x.val }

 theorem kernel_finite_negative [IsNoetherianRing R] : Module.Finite R[X] p.kernelSections.M0 := by
  change Module.Finite R[X] (LinearMap.ker p.negative)
  infer_instance

 theorem kernel_finite_positive [IsNoetherianRing R] : Module.Finite R[X] p.kernelSections.M1 := by
  change Module.Finite R[X] (LinearMap.ker p.positive)
  infer_instance

 def kernelInclusion0 : (p.kernelSections.M0 × p.kernelSections.M1) →ₗ[R]
    ((ι → R[X]) × (ι → R[X])) :=
  ((LinearMap.ker p.negative).subtype.restrictScalars R).prodMap
    ((LinearMap.ker p.positive).subtype.restrictScalars R)

 def kernelInclusion1 : p.kernelSections.M01 →ₗ[R] (ι → LaurentPolynomial R) :=
  (LinearMap.ker p.overlap).subtype.restrictScalars R

 theorem kernelInclusion1_injective : Function.Injective p.kernelInclusion1 := Subtype.val_injective

 theorem kernel_exact0 : Function.Exact p.kernelInclusion0 p.cochain0 := by
  intro z
  constructor
  · intro hz
    have h0 : p.negative z.1=0 := congrArg Prod.fst hz
    have h1 : p.positive z.2=0 := congrArg Prod.snd hz
    exact ⟨(⟨z.1,h0⟩,⟨z.2,h1⟩),rfl⟩
  · rintro ⟨x,rfl⟩
    exact Prod.ext x.1.property x.2.property

 theorem kernel_exact1 : Function.Exact p.kernelInclusion1 p.cochain1 := by
  intro z
  exact ⟨fun hz => ⟨⟨z,hz⟩,rfl⟩,fun ⟨x,hx⟩ => hx ▸ x.property⟩

 theorem kernel_cochain_comm : (freeTwistSections (R := R) (ι := ι) d).cechDiff.comp p.kernelInclusion0 =
    p.kernelInclusion1.comp p.kernelSections.cechDiff := by
  apply LinearMap.ext
  intro z
  rfl
end LaurentPresentation
end FourCorner.FiniteMapCohomology
