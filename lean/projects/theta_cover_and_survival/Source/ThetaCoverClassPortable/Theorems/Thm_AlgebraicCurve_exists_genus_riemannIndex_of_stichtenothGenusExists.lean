import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_Repartitions
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.P2M.Util
import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists

namespace AlgebraicCurve
theorem exists_genus_riemannIndex_of_stichtenothGenusExists {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (h : StichtenothGenusExists K F) :
    ∃ γ : ℤ, ∀ D : Divisor K F,
      Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ∧
        (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.solution
end AlgebraicCurve
