import ThetaCoverClassPortable.IdealFlatDescent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace Ideal
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The exact faithfully-flat ideal descent leaf used by affine relative
Cartier-divisor descent. The conclusion is proved from genuine tensor-ideal
invariance, not assumed as an effectiveness certificate. -/
theorem map_comap_eq_self_of_map_includeLeft_eq_map_includeRight
    [Module.FaithfullyFlat R S] (I : Ideal S)
    (hI : I.map (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S) =
      I.map (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom) :
    (I.comap (algebraMap R S)).map (algebraMap R S)=I :=
  FourCorner.IdealFlatDescent.map_comap_of_tensor_invariance I hI

end Ideal
#print axioms Ideal.map_comap_eq_self_of_map_includeLeft_eq_map_includeRight
