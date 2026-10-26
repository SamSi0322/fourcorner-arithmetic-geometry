import HpAxisQuadrics
import HpCanonicalIsomorphism

namespace FourCorner.HpDiagonalKernelRigidity
noncomputable section
variable {K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

abbrev V (K : Type*) := Fin 5 → K

def pair (d x y : V K) : K := ∑i,d i*x i*y i

def OnAxis (i : Fin 5) (x : V K) : Prop := ∀j,j ≠ i → x j=0

theorem onAxis_iff (i : Fin 5) (x : V K) : OnAxis i x ↔ x=x i • Pi.single i (1 : K) := by
  constructor
  · intro h
    ext j
    by_cases hj : j=i
    · subst j;simp
    · simp [Pi.smul_apply,Pi.single_apply,hj,h j hj]
  · intro h j hj
    rw [h]
    simp [Pi.smul_apply,Pi.single_apply,hj]

theorem kernel_iff (d x : V K) : (∀y,pair d x y=0) ↔ ∀i,d i*x i=0 := by
  constructor
  · intro h i
    simpa [pair,Pi.single_apply] using h (Pi.single i 1)
  · intro h y
    simp only [pair,← mul_assoc,h,zero_mul,Finset.sum_const_zero]

theorem kernel_single_zero (d : V K) (i : Fin 5) (hi : d i=0) (hn : ∀j,j ≠ i → d j ≠ 0) (x : V K) :
    (∀y,pair d x y=0) ↔ OnAxis i x := by
  rw [kernel_iff]
  constructor
  · intro h j hj
    exact (mul_eq_zero.mp (h j)).resolve_left (hn j hj)
  · intro h j
    by_cases hj : j=i
    · subst j;simp [hi]
    · simp [h j hj]

/-- The intrinsic one-dimensional kernels of the diagonal net force any
linear change preserving that net to carry every coordinate axis to an axis. -/
theorem inverse_axis (L : V K ≃ₗ[K] V K) (N : Set (V K))
    (haxes : ∀i : Fin 5,∃d∈N,d i=0 ∧ ∀j,j ≠ i → d j ≠ 0)
    (hpres : ∀d∈N,∃b : V K,∀x y,pair d (L x) (L y)=pair b x y)
    (i : Fin 5) : ∃j : Fin 5,OnAxis j (L.symm (Pi.single i 1)) := by
  obtain ⟨d,hd,hdi,hdn⟩ := haxes i
  obtain ⟨b,hb⟩ := hpres d hd
  let x := L.symm (Pi.single i 1)
  have hx0 : x ≠ 0 := by
    intro h
    have hh := congrArg L h
    simpa [x] using hh
  have hxr : ∀y,pair b x y=0 := by
    intro y
    rw [← hb]
    apply (kernel_single_zero d i hdi hdn _).mpr
    simp [x,OnAxis,Pi.single_apply]
  have hcomp : ∀j,b j*x j=0 := (kernel_iff b x).mp hxr
  obtain ⟨j,hj⟩ : ∃j,x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  have hbj : b j=0 := (mul_eq_zero.mp (hcomp j)).resolve_right hj
  have hej : ∀y,pair b (Pi.single j 1) y=0 := by
    apply (kernel_iff _ _).mpr
    intro k
    by_cases hk : k=j
    · subst k;simp [hbj]
    · simp [Pi.single_apply,hk]
  have hL : OnAxis i (L (Pi.single j 1)) := by
    apply (kernel_single_zero d i hdi hdn _).mp
    intro z
    obtain ⟨y,rfl⟩ := L.surjective z
    rw [hb]
    exact hej y
  have heq : Pi.single j (1 : K)=(L (Pi.single j 1)) i • x := by
    apply L.injective
    rw [map_smul,L.apply_symm_apply]
    exact (onAxis_iff i _).mp hL
  have hc : (L (Pi.single j 1)) i ≠ 0 := by
    intro h
    have hh := congrFun heq j
    simpa [h] using hh
  refine ⟨j,?_⟩
  intro k hk
  have hh := congrFun heq k
  have hz : (L (Pi.single j 1)) i*x k=0 := by
    simpa [Pi.smul_apply,Pi.single_apply,hk] using hh.symm
  exact (mul_eq_zero.mp hz).resolve_left hc

#print axioms kernel_iff
#print axioms inverse_axis
end
end FourCorner.HpDiagonalKernelRigidity
