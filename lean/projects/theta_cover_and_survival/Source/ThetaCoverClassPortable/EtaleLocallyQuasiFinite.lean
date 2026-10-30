import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Unramified.LocalStructure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open AlgebraicGeometry
namespace FourCorner.ThetaLocalSurvival.Multiplication

/-- A genuine missing scheme-level algebraic bridge: etale morphisms
are locally quasi-finite. It is proved on actual affine section rings
using the native unramified finite-fibre theorem. -/
theorem etale_locallyQuasiFinite {X Y : Scheme} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  let g := (f.appLE U V e).hom
  letI := g.toAlgebra
  haveI : Algebra.Etale Γ(Y,U) Γ(X,V) := (f.etale_appLE hU hV e).toAlgebra
  change Algebra.QuasiFinite Γ(Y,U) Γ(X,V)
  infer_instance

end FourCorner.ThetaLocalSurvival.Multiplication
