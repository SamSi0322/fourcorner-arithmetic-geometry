import HpLiteralGeometricNoniso

namespace FourCorner.HpLiteralGeometricNonisoAudit
open HpGeometricIsoFibres

/-- Exact missing clause of thm:hp-infinite for the original literal C_p:
the displayed p_j yield infinitely many UNMARKED geometric curve classes. -/
theorem original_family_infinite_geometric_classes :
    Set.Infinite (Set.range (fun j : ℕ => Quotient.mk HpLiteralGeometricNoniso.geometricSetoid (familyParameter j))) :=
  HpLiteralGeometricNoniso.infinitely_many_geometric_classes

#print axioms original_family_infinite_geometric_classes
#print axioms FourCorner.HpLiteralGeometricNoniso.finite_geometric_iso_fibre
#print axioms FourCorner.HpLiteralGeometricNoniso.objectIso
#print axioms FourCorner.HpLiteralGeometric.geometricIso
#print axioms FourCorner.HpLiteralGeometric.geometricIso_over
#print axioms FourCorner.HpNativeBranchEquivalence.equivalent_of_field_iso
#print axioms FourCorner.HpBranchLinearDescent.actual_branch_matrix
#print axioms FourCorner.HpActualMonomial.actual_monomial
#print axioms FourCorner.HpCanonicalNetPreservation.actual_inverse_axis
#print axioms FourCorner.HpCanonicalNetPreservation.net_preservation
#print axioms FourCorner.HpQuadraticRelations.quadratic_relation_iff
#print axioms FourCorner.HpDiagonalNet.net_finrank
#print axioms FourCorner.HpCanonicalBasis.basis
#print axioms FourCorner.HpRootProductBasis.basis
#print axioms FourCorner.HpDifferentialTransport.pullback_regular
end FourCorner.HpLiteralGeometricNonisoAudit
