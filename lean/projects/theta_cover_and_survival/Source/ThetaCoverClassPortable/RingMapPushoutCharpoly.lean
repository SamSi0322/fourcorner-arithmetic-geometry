import ThetaCoverClassPortable.RingMapTensorPushout
import ThetaCoverClassPortable.ProjectiveAmbientBaseChange

namespace FourCorner.RingMapTensorPushout
open FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The SAME original finite-free ambient presentation base-changes into
the ACTUAL native pushout. Its padded characteristic polynomial is the
original polynomial mapped along the original scalar ring homomorphism. -/
theorem ambientCharpoly_pushout (f : R →+* S) (g : R →+* T)
    (p : letI := g.toAlgebra;Frame R T) (b : T) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := pointAlgebra f g
    ambientCharpoly (pushoutFrame f g p) (LinearMap.mulLeft S ((right f g).hom b))=
      (ambientCharpoly p (LinearMap.mulLeft R b)).map f := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := pointAlgebra f g
  exact (ambientCharpoly_transport (baseChangeFrame S p) (tensorEquiv f g).toLinearEquiv
    ((LinearMap.mulLeft R b).baseChange S) (LinearMap.mulLeft S ((right f g).hom b))
    (multiplication_intertwines f g b)).trans (ambientCharpoly_baseChange S p (LinearMap.mulLeft R b))

#print axioms ambientCharpoly_pushout
end
end FourCorner.RingMapTensorPushout
