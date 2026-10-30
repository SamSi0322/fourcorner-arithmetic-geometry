import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Definitions.Def_ModularCurve_CanonicalDivisor
import ThetaCoverClassPortable.P2M.Util
import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental

open IntermediateField Algebra

namespace AlgebraicCurve
namespace IsCurveOver

theorem exists_separating_transcendental {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.solution
