import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
set_option autoImplicit false
namespace AlgebraicCurve.Place
theorem mem_toValuationSubring_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring :=
  P2MW.S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin.solution v hj hx
end AlgebraicCurve.Place
#print axioms AlgebraicCurve.Place.mem_toValuationSubring_of_isIntegral_adjoin
