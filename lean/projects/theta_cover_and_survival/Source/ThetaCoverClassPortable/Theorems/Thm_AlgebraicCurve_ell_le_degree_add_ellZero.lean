import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_ell_le_degree_add_ellZero
set_option autoImplicit false
namespace AlgebraicCurve
theorem ell_le_degree_add_ellZero {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {D : Divisor K F} (hD : 0 ≤ D) [FiniteDimensional K (LSpace (0 : Divisor K F))] :
    (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) :=
  P2MW.S_AlgebraicCurve_ell_le_degree_add_ellZero.solution hD
end AlgebraicCurve
#print axioms AlgebraicCurve.ell_le_degree_add_ellZero
