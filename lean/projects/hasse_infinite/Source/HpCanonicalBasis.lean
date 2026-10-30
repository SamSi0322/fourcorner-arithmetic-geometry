import HpRootProductBasis

namespace FourCorner.HpCanonicalBasis
open AlgebraicCurve HpLiteralField HpFieldGeometry HpCanonicalForms HpRootProductBasis
noncomputable section
variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
attribute [local instance] Classical.propDecidable
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule

def coordinateSupport : Fin 5 → Finset (Fin 4) := ![{0},{1},{2},{3},∅]
def denominatorSupport : Fin 5 → Finset (Fin 4) :=
  ![Finset.univ.erase 0,Finset.univ.erase 1,Finset.univ.erase 2,Finset.univ.erase 3,Finset.univ]

def coordinate (p : K) (i : Fin 5) : field K p := monomial K p (coordinateSupport i)

theorem coordinateSupport_injective : Function.Injective coordinateSupport := by decide

@[simp] theorem coordinate_zero (p : K) : coordinate K p 0=root K p 0 := by simp [coordinate,coordinateSupport,monomial]
@[simp] theorem coordinate_one (p : K) : coordinate K p 1=root K p 1 := by simp [coordinate,coordinateSupport,monomial]
@[simp] theorem coordinate_two (p : K) : coordinate K p 2=root K p 2 := by simp [coordinate,coordinateSupport,monomial]
@[simp] theorem coordinate_three (p : K) : coordinate K p 3=root K p 3 := by simp [coordinate,coordinateSupport,monomial]
@[simp] theorem coordinate_four (p : K) : coordinate K p 4=1 := by simp [coordinate,coordinateSupport,monomial]

theorem coordinates_independent (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    LinearIndependent K (coordinate K p) :=
  ((monomials_linearIndependent K p hp ha hb).comp coordinateSupport coordinateSupport_injective).restrict_scalars' K

def differential (p : K) (i : Fin 5) : Ω[field K p⁄K] := form K p (denominatorSupport i)

theorem differential_regular (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 5) :
    differential K p i ∈ regularDifferentials K (field K p) := by
  apply form_regular K p hp ha hb
  fin_cases i <;> decide

theorem root_smul_fullForm (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 4) :
    root K p i • form K p Finset.univ=form K p (Finset.univ.erase i) := by
  unfold form
  rw [smul_smul]
  congr 1
  have hh : root K p i / rootProduct K p Finset.univ=1 / rootProduct K p (Finset.univ.erase i) := by
    apply (div_eq_div_iff (rootProduct_ne_zero K p hp ha hb _) (rootProduct_ne_zero K p hp ha hb _)).mpr
    simpa [rootProduct] using Finset.mul_prod_erase Finset.univ (root K p) (Finset.mem_univ i)
  simpa only [div_eq_mul_inv,one_mul] using hh

/-- Ratios to the last differential are literally the four original roots and one. -/
theorem differential_eq_coordinate_smul (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 5) :
    differential K p i=coordinate K p i • form K p Finset.univ := by
  fin_cases i
  · simpa [differential,denominatorSupport] using (root_smul_fullForm K p hp ha hb 0).symm
  · simpa [differential,denominatorSupport] using (root_smul_fullForm K p hp ha hb 1).symm
  · simpa [differential,denominatorSupport] using (root_smul_fullForm K p hp ha hb 2).symm
  · simpa [differential,denominatorSupport] using (root_smul_fullForm K p hp ha hb 3).symm
  · simp [differential,denominatorSupport]

theorem differentials_independent (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    LinearIndependent K (differential K p) := by
  let T : field K p →ₗ[K] Ω[field K p⁄K] :=
    { toFun := fun f => f • form K p Finset.univ
      map_add' := fun a b => add_smul a b _
      map_smul' := fun c f => smul_assoc c f _ }
  have hi : Function.Injective T := by
    intro a b hab
    apply sub_eq_zero.mp
    have hz : (a-b) • form K p Finset.univ=0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr hab
    exact (smul_eq_zero.mp hz).resolve_right (form_ne_zero K p hp ha hb _)
  have h := (coordinates_independent K p hp ha hb).map' T (LinearMap.ker_eq_bot.mpr hi)
  have he : differential K p=T ∘ coordinate K p := funext fun i => differential_eq_coordinate_smul K p hp ha hb i
  rw [he]
  exact h

def regularVector (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 5) :
    regularDifferentials K (field K p) := ⟨differential K p i,differential_regular K p hp ha hb i⟩

theorem regularVectors_independent (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    LinearIndependent K (regularVector K p hp ha hb) := by
  apply LinearIndependent.of_comp (f := (regularDifferentials K (field K p)).subtype)
  exact differentials_independent K p hp ha hb

/-- The five displayed forms are an actual basis of the intrinsic regular-differential space. -/
def basis (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    Module.Basis (Fin 5) K (regularDifferentials K (field K p)) := by
  letI := (regular_space_dimension K p hp ha hb).1
  apply basisOfLinearIndependentOfCardEqFinrank (regularVectors_independent K p hp ha hb)
  simpa using (regular_space_dimension K p hp ha hb).2.symm

@[simp] theorem basis_coe (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 5) :
    ((basis K p hp ha hb i : regularDifferentials K (field K p)) : Ω[field K p⁄K])=differential K p i := by
  simp [basis,basisOfLinearIndependentOfCardEqFinrank,regularVector,Module.Basis.mk_apply]

#print axioms coordinates_independent
#print axioms differential_regular
#print axioms differentials_independent
#print axioms basis
end
end FourCorner.HpCanonicalBasis
