import HpGeometricIsoFibres

/-! Kernel-facing entry for the formerly missing geometric-isomorphism
clause. The equivalence relation is native unmarked isomorphism over Qbar
of the actual constant-base-changed curve models. -/
namespace FourCorner.HpGeometricNoniso
open HpGeometricIsoFibres

 theorem thm_hp_infinite_geometric_nonisomorphism :
    Set.Infinite (Set.range (fun j : ℕ => Quotient.mk geometricSetoid (familyParameter j))) :=
  infinitely_many_geometric_classes

#print axioms thm_hp_infinite_geometric_nonisomorphism
#print axioms FourCorner.HpCanonicalForms.rhoDiff_order
#print axioms FourCorner.HpCanonicalBasis.basis
#print axioms FourCorner.HpRootProductBasis.basis
#print axioms FourCorner.HpQuadraticRelations.quadratic_relation_iff
#print axioms FourCorner.HpDiagonalNet.net_finrank
#print axioms FourCorner.HpAxisQuadrics.exists_unique_zero_coefficient
#print axioms FourCorner.HpCanonicalNetPreservation.net_preservation
#print axioms FourCorner.HpCanonicalNetPreservation.actual_inverse_axis
#print axioms FourCorner.HpActualMonomial.actual_monomial
#print axioms FourCorner.HpBranchLinearDescent.actual_branch_matrix
#print axioms FourCorner.HpNativeBranchEquivalence.equivalent_of_field_iso
#print axioms FourCorner.HpGeometricIsoFibres.literalFieldEquiv
#print axioms FourCorner.HpGeometricIsoFibres.finite_geometric_iso_fibre
end FourCorner.HpGeometricNoniso
