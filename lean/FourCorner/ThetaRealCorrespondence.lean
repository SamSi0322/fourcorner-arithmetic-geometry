import FourCorner.ThetaRealCorrespondenceCore
import Mathlib.Tactic.Ext

/-! The full real metric correspondence in Section 7, including both inverse
maps, all four labelled radii, and exact positivity/interior conditions. -/
namespace FourCorner
noncomputable section

@[ext] structure ThetaRealSourcePoint where
  P : ℝ
  Q : ℝ
  R : ℝ
  z : ℝ

@[ext] structure ThetaRealConfiguration where
  x : ℝ
  y : ℝ
  r0 : ℝ
  r1 : ℝ
  r2 : ℝ
  r3 : ℝ

def ThetaRealSourcePoint.Valid (s : ThetaRealSourcePoint) : Prop :=
  RealThetaPositiveSource s.P s.Q s.R s.z

def ThetaRealConfiguration.Valid (c : ThetaRealConfiguration) : Prop :=
  RealStrictPoint c.x c.y c.r0 c.r1 c.r2 c.r3 ∧ c.r3-c.r0=1/5

/-- The literal ordered metric return in the paper. -/
def ThetaRealSourcePoint.toConfiguration (s : ThetaRealSourcePoint) : ThetaRealConfiguration :=
  ⟨(50-s.P-7*s.z)/100, (50-s.P+7*s.z)/100,
    (s.P-1)/10, s.Q/10, s.R/10, (s.P+1)/10⟩

/-- The actual inverse, using all four radii of the same real configuration. -/
def ThetaRealConfiguration.toSource (c : ThetaRealConfiguration) : ThetaRealSourcePoint :=
  ⟨5*(c.r3+c.r0), 10*c.r1, 10*c.r2, 50*(c.y-c.x)/7⟩

theorem theta_real_return_valid {s : ThetaRealSourcePoint} (hs : s.Valid) :
    s.toConfiguration.Valid := by
  refine ⟨real_theta_positive_source_to_strict_point hs, ?_⟩
  change (s.P+1)/10-(s.P-1)/10=(1:ℝ)/5
  ring

theorem theta_real_inverse_valid {c : ThetaRealConfiguration} (hc : c.Valid) :
    c.toSource.Valid := by
  exact real_strict_point_difference_to_theta_positive_source hc.1 hc.2

/-- Applying the explicit inverse to the return recovers all four source coordinates. -/
theorem theta_real_inverse_return (s : ThetaRealSourcePoint) :
    s.toConfiguration.toSource = s := by
  apply ThetaRealSourcePoint.ext <;>
    dsimp [ThetaRealSourcePoint.toConfiguration,ThetaRealConfiguration.toSource] <;> ring

/-- Returning from the reconstructed source recovers the original point and
all four labelled real radii. -/
theorem theta_real_return_inverse {c : ThetaRealConfiguration} (hc : c.Valid) :
    c.toSource.toConfiguration = c := by
  obtain ⟨hx,hy,hr0,hr3⟩ := real_strict_point_difference_inverse_coordinates hc.1 hc.2
  apply ThetaRealConfiguration.ext
  · exact hx.symm
  · exact hy.symm
  · exact hr0.symm
  · change 10*c.r1/10=c.r1
    ring
  · change 10*c.r2/10=c.r2
    ring
  · exact hr3.symm

/-- Full real bijection claimed in Section 7: the positive source U is exactly
the strict four-distance locus with opposite radius difference 1/5. -/
def theta_real_correspondence :
    {s : ThetaRealSourcePoint // s.Valid} ≃ {c : ThetaRealConfiguration // c.Valid} where
  toFun s := ⟨s.val.toConfiguration,theta_real_return_valid s.property⟩
  invFun c := ⟨c.val.toSource,theta_real_inverse_valid c.property⟩
  left_inv s := Subtype.ext (theta_real_inverse_return s.val)
  right_inv c := Subtype.ext (theta_real_return_inverse c.property)

/-- The positive source point is unique for a given strict labelled configuration. -/
theorem theta_real_unique_source {c : ThetaRealConfiguration} (hc : c.Valid) :
    ∃! s : ThetaRealSourcePoint, s.Valid ∧ s.toConfiguration=c := by
  refine ⟨c.toSource, ⟨theta_real_inverse_valid hc,theta_real_return_inverse hc⟩, ?_⟩
  intro s hs
  have hh := congrArg ThetaRealConfiguration.toSource hs.2
  rwa [theta_real_inverse_return s] at hh

#print axioms theta_real_return_valid
#print axioms theta_real_inverse_valid
#print axioms theta_real_inverse_return
#print axioms theta_real_return_inverse
#print axioms theta_real_correspondence
#print axioms theta_real_unique_source
end
end FourCorner
