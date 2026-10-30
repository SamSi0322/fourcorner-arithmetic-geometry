import ThetaCoverClassPortable.HasseReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_Repartitions
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.P2M.Util
import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_one_le_deg

namespace AlgebraicCurve
theorem one_le_deg {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_one_le_deg.solution
end AlgebraicCurve
