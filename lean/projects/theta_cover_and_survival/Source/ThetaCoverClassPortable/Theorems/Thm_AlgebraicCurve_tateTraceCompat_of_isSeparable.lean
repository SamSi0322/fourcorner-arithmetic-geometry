import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Definitions.Def_ModularCurve_CanonicalDivisor
import ThetaCoverClassPortable.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_Repartitions
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_LocalResidue
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ThetaCoverClassPortable.Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_PlaceCompletion
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_TateResidueCurrency
import ThetaCoverClassPortable.P2M.Util
import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_tateTraceCompat_of_isSeparable

theorem AlgebraicCurve.tateTraceCompat_of_isSeparable
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] [Algebra.IsSeparable E F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue] [∀ v : AlgebraicCurve.Place K E, v.FiniteResidue]
    (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F)
    (hfinE : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K E) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateTraceCompat K F E hfinF hfinE := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.solution
