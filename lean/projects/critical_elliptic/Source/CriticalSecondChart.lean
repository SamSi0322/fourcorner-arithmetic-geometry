import CriticalAffineDomain
import CriticalStandardCharts

noncomputable section
namespace FourCorner.CriticalSecondChart
open MvPolynomial CriticalStandardCharts
variable {k : Type*} [Field k]

def swapVariables : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k :=
  MvPolynomial.renameEquiv k (Equiv.swap 1 2)

theorem equation_swap (i : k) (a : Fin 2) :
    swapVariables (affineEquation i 1 a)=CriticalAffineGeometry.equation (-i) a.rev := by
  have hs : Equiv.swap (1:Fin 3) 2 0=0 := by decide
  fin_cases a <;> simp [hs,swapVariables,affineEquation,CriticalQuotientChart.affineEquation,
    CriticalAmbientChart.dehom,CriticalAmbientChart.drop,CriticalProj23.equation,
    CriticalProj23.F0,CriticalProj23.F1,CriticalAffineGeometry.equation] <;> ring

theorem ideal_swap (i : k) : Ideal.map (swapVariables (k:=k)).toRingHom (affineIdeal i 1)=
    CriticalAffineGeometry.ideal (-i) := by
  rw [Ideal.map_span,←Set.range_comp']
  have hfun : (swapVariables (k:=k)).toRingHom ∘ affineEquation i 1 =
      fun a=>CriticalAffineGeometry.equation (-i) a.rev := funext (equation_swap i)
  change Ideal.span (Set.range ((swapVariables (k:=k)).toRingHom ∘ affineEquation i 1))=_
  rw [hfun]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨a,rfl⟩; exact ⟨a.rev,rfl⟩
  · rintro ⟨a,rfl⟩; exact ⟨a.rev,by simp⟩

/-- V1=1 is the same literal affine presentation at -i, with the two final
coordinates exchanged. No square roots or scalar-extension choices occur. -/
def equiv (i : k) : affineRing i 1 ≃ₐ[k] CriticalAffineGeometry.ring (-i) :=
  Ideal.quotientEquivAlg (affineIdeal i 1) (CriticalAffineGeometry.ideal (-i))
    swapVariables (ideal_swap i).symm

theorem isDomain (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) : IsDomain (affineRing i 1) := by
  letI := CriticalAffineDomain.ring_isDomain (-i) (by simpa only [neg_sq] using hi) h2
  exact Function.Injective.isDomain (equiv i).toRingHom (equiv i).injective
end FourCorner.CriticalSecondChart
#print axioms FourCorner.CriticalSecondChart.equiv
#print axioms FourCorner.CriticalSecondChart.isDomain
