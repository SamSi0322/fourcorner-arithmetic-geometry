import ThetaCoverClassPortable.NativeRealEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology
namespace FourCorner.ThetaSurvivingNativeRealPath
open ThetaLiteralModels
open ThetaLocalSurvival.StrongTopology ThetaLocalSurvival.Infinitesimal ThetaLocalSurvival.Multiplication

/-- The ORIGINAL C's actual T-nonzero open subscheme, with its actual QQ structure map. -/
def tOpenObject : Over base := Over.mk (sourceTOpen.ι≫cToBase ℚ)
def tOpenInclusion : tOpenObject ⟶ sourceObject := Over.homMk sourceTOpen.ι rfl

instance tOpenInclusion_isOpenImmersion : IsOpenImmersion tOpenInclusion.left :=
  inferInstanceAs (IsOpenImmersion sourceTOpen.ι)

/-- The endpoint as a genuine real point of the actual T-nonzero open subscheme. -/
def endpointInTOpen : KPoints ℝ tOpenObject :=
  openPointLift ℝ tOpenInclusion endpoint (by
    change pointSupport ℝ endpoint∈Set.range sourceTOpen.ι
    rw [Scheme.Opens.range_ι]
    exact endpoint_T_nonzero)

@[simp] theorem endpointInTOpen_inclusion : endpointInTOpen≫tOpenInclusion=endpoint :=
  openPointLift_comp ℝ tOpenInclusion endpoint _

/-- The strict real set is a subset of actual real points of the actual open C\(T=0). -/
def strictRealSet : Set (KPoints ℝ tOpenObject) := {P | P≫tOpenInclusion∈paperU}

/-- The exact real-set/path hypothesis consumable by local survival, with no assigned topology. -/
theorem strictRealSet_has_joined_point :
    ∃ P∈strictRealSet,Joined (rationalScalarPoint ℝ originalOrigin) (P≫tOpenInclusion) := by
  refine ⟨endpointInTOpen,?_,?_⟩
  · change endpointInTOpen≫tOpenInclusion∈paperU
    rw [endpointInTOpen_inclusion]
    exact endpoint_mem_paperU
  · rw [endpointInTOpen_inclusion]
    exact ⟨originalRealPath⟩

/-- Native real path package for cor:theta-surviving-covers. The source curve, original OC,
open subscheme, canonical strong topology and all point maps are literal. This theorem
does not assert Jacobian representability or any surviving-cover conclusion. -/
theorem native_real_path_package :
    Nonempty (Path (rationalScalarPoint ℝ originalOrigin) endpoint) ∧
    endpointInTOpen≫tOpenInclusion=endpoint ∧ endpoint∈paperU ∧
    endpointY-endpointX=7/300 ∧ endpointX≠endpointY ∧
    (∃ P∈strictRealSet,Joined (rationalScalarPoint ℝ originalOrigin) (P≫tOpenInclusion)) :=
  ⟨⟨originalRealPath⟩,endpointInTOpen_inclusion,endpoint_mem_paperU,endpoint_y_sub_x,
    endpoint_x_ne_y,strictRealSet_has_joined_point⟩

end FourCorner.ThetaSurvivingNativeRealPath
