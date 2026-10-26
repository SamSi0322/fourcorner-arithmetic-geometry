import HpLiteralSmooth
import HpFourRootUniversal

namespace FourCorner.HpAffineUniversal
open MvPolynomial Polynomial HpLiteralField HpLiteralProjective HpLiteralSmooth
noncomputable section
variable (K : Type*) [Field K] [CharZero K]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

abbrev A (p : K) := HpPolynomialRootAlgebra.A K p
abbrev B (p : K) := HpLiteralProjective.affineRing K p 0

def coeff (p : K) : K →+* A K p := (algebraMap K[X] (A K p)).comp Polynomial.C
def rhoA (p : K) : A K p := algebraMap K[X] (A K p) Polynomial.X
abbrev rootA (p : K) := FourRootLift08.coord K[X] (HpLiteralField.poly K p)

theorem rootA_sq (p : K) (i : Fin 4) :
    (rootA K p i)^2=HpResidueCharts.values (coeff K p p) (rhoA K p) i := by
  rw [HpFourRootUniversal.coord_sq]
  fin_cases i <;> simp only [HpLiteralField.poly,HpResidueCharts.values,map_mul,map_add,map_sub,
    map_one,map_ofNat,coeff,RingHom.comp_apply,rhoA]
  all_goals ring

def evalA (p : K) : MvPolynomial (Fin 4) K →+* A K p := eval₂Hom (coeff K p) (rootA K p)

theorem evalA_relations (p : K) (i : Fin 3) :
    evalA K p (ThetaQuotientChart.affineEquation (equation K p) 0 i)=0 := by
  have h0 := rootA_sq K p 0
  have h1 := rootA_sq K p 1
  have h2 := rootA_sq K p 2
  have h3 := rootA_sq K p 3
  change (rootA K p 0)^2=coeff K p p*rhoA K p at h0
  change (rootA K p 1)^2=2*(coeff K p p-1)*(rhoA K p-1) at h1
  change (rootA K p 2)^2=2*(coeff K p p+1)*(rhoA K p+1) at h2
  change (rootA K p 3)^2=(coeff K p p-1)*rhoA K p+coeff K p p+1 at h3
  fin_cases i
  all_goals simp [evalA,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,equation,
    HpLiteralSmooth.drop_table,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat]
  · rw [h1,h0];ring
  · rw [h2,h0];ring
  · rw [h3,h0];ring

def toUniversal (p : K) : B K p →+* A K p :=
  Ideal.Quotient.lift _ (evalA K p) (by
    have hk : ThetaQuotientChart.affineIdeal (equation K p) 0 ≤ RingHom.ker (evalA K p) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact evalA_relations K p i
    exact fun a ha=>hk ha)

@[simp] theorem toUniversal_X (p : K) (i : Fin 4) :
    toUniversal K p (Ideal.Quotient.mk _ (MvPolynomial.X i))=rootA K p i := by
  exact MvPolynomial.eval₂_X _ _ _
@[simp] theorem toUniversal_C (p c : K) :
    toUniversal K p (algebraMap K (B K p) c)=coeff K p c := by
  change toUniversal K p (Ideal.Quotient.mk _ (MvPolynomial.C c))=coeff K p c
  exact MvPolynomial.eval₂_C _ _ _

#print axioms rootA_sq
#print axioms evalA_relations
#print axioms toUniversal
end
end FourCorner.HpAffineUniversal
