import ThetaCoverClassPortable.ModuleColimitWitness
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

noncomputable section
open scoped TensorProduct
universe u v w z s
namespace FourCorner.FPDescent

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]
  [DecidableEq ι] [Nonempty ι] [IsDirectedOrder ι]
  {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
  [DirectedSystem G (fun i j h => f i j h)]
  {M : Type z} [AddCommGroup M] [Module R M]

/-- The concrete surjectivity/eventual-zero data identify the genuine native
direct limit, rather than an assumed universal-property substitute. -/
def moduleColimitEquiv (W : ModuleColimitWitness R ι G f M) :
    Module.DirectLimit G f ≃ₗ[R] M := by
  let l := Module.DirectLimit.lift R ι G f W.incl
    (fun i j h x => LinearMap.congr_fun (W.comm i j h) x)
  refine LinearEquiv.ofBijective l ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero l).mpr
    intro x hx
    obtain ⟨i,a,rfl⟩ := Module.DirectLimit.exists_of x
    have ha : W.incl i a = 0 := by simpa [l] using hx
    obtain ⟨j,hij,hj⟩ := W.vanish i a ha
    rw [← Module.DirectLimit.of_f (f := f) (hij := hij), hj, map_zero]
  · intro x
    obtain ⟨i,a,ha⟩ := W.surj x
    exact ⟨Module.DirectLimit.of R ι G f i a, by simpa [l] using ha⟩

@[simp] theorem moduleColimitEquiv_of (W : ModuleColimitWitness R ι G f M)
    (i : ι) (x : G i) :
    moduleColimitEquiv W (Module.DirectLimit.of R ι G f i x) = W.incl i x := by
  change Module.DirectLimit.lift R ι G f W.incl
    (fun i j h x => LinearMap.congr_fun (W.comm i j h) x)
    (Module.DirectLimit.of R ι G f i x) = W.incl i x
  exact Module.DirectLimit.lift_of _ _ x

variable (N : Type s) [AddCommGroup N] [Module R N]

/-- Tensor the real colimit comparison through the native tensor/direct-limit
equivalence. No flatness or finite presentation of N is needed. -/
def tensorColimitEquiv (W : ModuleColimitWitness R ι G f M) :
    Module.DirectLimit (fun i => G i ⊗[R] N)
      (fun i j h => (f i j h).rTensor N) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft f N).symm ≪≫ₗ (moduleColimitEquiv W).rTensor N

@[simp] theorem tensorColimitEquiv_of (W : ModuleColimitWitness R ι G f M)
    (i : ι) (x : G i ⊗[R] N) :
    tensorColimitEquiv N W
      (Module.DirectLimit.of R ι (fun i => G i ⊗[R] N)
        (fun i j h => (f i j h).rTensor N) i x) = (W.incl i).rTensor N x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => simp [tensorColimitEquiv]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensoring the actual directed system preserves its concrete colimit
criterion; eventual-zero exactness is derived by native direct-limit exactness. -/
def tensorColimitWitness (W : ModuleColimitWitness R ι G f M) :
    ModuleColimitWitness R ι (fun i => G i ⊗[R] N)
      (fun i j h => (f i j h).rTensor N) (M ⊗[R] N) where
  incl i := (W.incl i).rTensor N
  comm i j h := by
    rw [← LinearMap.rTensor_comp, W.comm i j h]
  surj x := by
    obtain ⟨z,hz⟩ := (tensorColimitEquiv N W).surjective x
    obtain ⟨i,y,rfl⟩ := Module.DirectLimit.exists_of z
    exact ⟨i,y,by simpa using hz⟩
  vanish i x hx := by
    have hz : Module.DirectLimit.of R ι (fun i => G i ⊗[R] N)
        (fun i j h => (f i j h).rTensor N) i x = 0 := by
      apply (tensorColimitEquiv N W).injective
      simpa using hx
    exact Module.DirectLimit.of.zero_exact hz

end FourCorner.FPDescent
