import ActualLogCharacter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open ChabautyColeman

private theorem formalLaw_ext {R : Type*} [CommRing R]
    (Phi Psi : FormalGroupLaw R Unit) (h : Phi.F=Psi.F) : Phi=Psi := by
  cases Phi
  cases Psi
  cases h
  rfl

/-- The actual chord formal group law commutes with coefficient base change. -/
theorem formalGroupLaw_map {R S : Type*} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (f : R →+* S) :
    W.formalGroupLaw.map f=(W.map f).formalGroupLaw := by
  apply formalLaw_ext
  funext i
  change MvPowerSeries.map f W.addSeries=(W.map f).addSeries
  exact W.map_addSeries f

/-- The literal log series uses the formal law of precisely the original
rational congruent model after its canonical embedding into Q_2. -/
theorem logIntegralCurve_formalField (n : ℤ) :
    (logIntegralCurve n).formalGroupLaw.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])=
      ((congruentCurve (n:ℚ)).map (Rat.castHom ℚ_[2])).formalGroupLaw := by
  rw [formalGroupLaw_map,logIntegralCurve_field]

theorem literalLog_original_curve (n : ℤ) :
    literalLog (logIntegralCurve n).formalGroupLaw=
      ((congruentCurve (n:ℚ)).map (Rat.castHom ℚ_[2])).formalGroupLaw.log () := by
  unfold literalLog
  rw [logIntegralCurve_formalField]

#print axioms formalGroupLaw_map
#print axioms logIntegralCurve_formalField
#print axioms literalLog_original_curve
end FourCorner.CommonSource.LogPrecision
