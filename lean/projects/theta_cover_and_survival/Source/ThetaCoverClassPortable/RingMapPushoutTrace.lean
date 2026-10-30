import ThetaCoverClassPortable.RingMapTensorPushout
import ThetaCoverClassPortable.ProjectiveTraceBaseChange

namespace FourCorner.RingMapTensorPushout
open FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

 theorem traceAlong_pushout (f : R →+* S) (g : R →+* T)
    (p : letI := g.toAlgebra;Frame R T) (b : T) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := pointAlgebra f g
    traceAlong (pushoutFrame f g p) (LinearMap.mulLeft S ((right f g).hom b))=
      f (traceAlong p (LinearMap.mulLeft R b)) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := pointAlgebra f g
  exact (traceAlong_transport (baseChangeFrame S p) (tensorEquiv f g).toLinearEquiv
    ((LinearMap.mulLeft R b).baseChange S) (LinearMap.mulLeft S ((right f g).hom b))
    (multiplication_intertwines f g b)).trans (traceAlong_baseChange S p (LinearMap.mulLeft R b))

#print axioms traceAlong_pushout
end
end FourCorner.RingMapTensorPushout
