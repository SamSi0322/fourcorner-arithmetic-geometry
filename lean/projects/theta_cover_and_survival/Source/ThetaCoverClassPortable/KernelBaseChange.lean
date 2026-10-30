import ThetaCoverClassPortable.FlatTargetTensor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCech

namespace FourCorner.MumfordKernel
noncomputable section
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R]
variable {C0 C1 : Type v} [AddCommGroup C0] [AddCommGroup C1] [Module R C0] [Module R C1]

/-- The LITERAL original kerBaseChangeHom is bijective for EVERY algebra,
including nonflat/nonnoetherian S. Flatness of the TARGET C1, not S/R,
proves injectivity; genuine tensor right-exactness proves surjectivity. -/
theorem kernel_baseChange_bijective [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (hd : Function.Surjective d)
    (S : Type w) [CommRing S] [Algebra R S] :
    Function.Bijective (TwoChartCech.kerBaseChangeHom d S) := by
  constructor
  · intro x y h
    apply tensor_kernel_subtype_injective d hd S
    exact congrArg Subtype.val h
  · intro x
    have he := lTensor_exact S d.exact_subtype_ker_map hd
    have hx : d.lTensor S (x : S ⊗[R] C0)=0 := x.property
    obtain ⟨y,hy⟩ := (he (x : S ⊗[R] C0)).mp hx
    exact ⟨y,Subtype.ext hy⟩

#print axioms kernel_baseChange_bijective
end
end FourCorner.MumfordKernel
