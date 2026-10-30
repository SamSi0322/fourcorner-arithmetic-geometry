import HasseBranchConfiguration
import ProjectiveActionFinite

noncomputable section
set_option autoImplicit false
namespace FourCorner.HasseRationalBranchFiniteness
open ProjectiveThreePoint HasseBranchConfiguration
variable {K:Type*} [Field K] [CharZero K]

def rationalEquivalent (p q:ℚ):Prop:=Equivalent (K:=K) (by norm_num) (p:K) (q:K)

/-- Rational parameters remain injective after their actual coefficient map
into any characteristic-zero field, including the algebraic closure of Q. -/
theorem rational_parameter_injective:
 Function.Injective (fun p:ℚ=>parameter (K:=K) (by norm_num) (p:K)):=
 (parameter_injective (by norm_num)).comp Rat.cast_injective

/-- Genuine unordered native projective branch equivalence has finite
rational fibres. This is a conclusion from that equivalence, not an assumed
automorphism finiteness or a replacement for the curve-isomorphism bridge. -/
theorem finite_rational_fibre (q:ℚ):{p:ℚ|rationalEquivalent (K:=K) p q}.Finite:=by
 have h:=finite_parameter_fibre (K:=K) (by norm_num) (q:K)
 exact h.preimage (f:=fun p:ℚ=>(p:K)) Rat.cast_injective.injOn

theorem finite_positive_rational_fibre (q:ℚ):
 {p:ℚ|1<p ∧rationalEquivalent (K:=K) p q}.Finite:=
 (finite_rational_fibre (K:=K) q).subset (by intro p hp;exact hp.2)

#print axioms rational_parameter_injective
#print axioms finite_rational_fibre
#print axioms finite_positive_rational_fibre
end FourCorner.HasseRationalBranchFiniteness
