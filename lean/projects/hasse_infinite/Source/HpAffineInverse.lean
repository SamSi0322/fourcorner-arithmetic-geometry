import HpAffineUniversal

namespace FourCorner.HpAffineInverse
open Polynomial MvPolynomial HpLiteralField HpLiteralProjective HpAffineUniversal
noncomputable section
variable (K : Type*) [Field K] [CharZero K]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

abbrev x (p : K) (i : Fin 4) : B K p := Ideal.Quotient.mk _ (MvPolynomial.X i)
def rhoB (p : K) : B K p := algebraMap K (B K p) p⁻¹*(x K p 0)^2

theorem relations (p : K) :
    (algebraMap K (B K p) p)*(x K p 1)^2=
      2*(algebraMap K (B K p) p-1)*((x K p 0)^2-algebraMap K (B K p) p) ∧
    (algebraMap K (B K p) p)*(x K p 2)^2=
      2*(algebraMap K (B K p) p+1)*((x K p 0)^2+algebraMap K (B K p) p) ∧
    (algebraMap K (B K p) p)*(x K p 3)^2=
      (algebraMap K (B K p) p-1)*(x K p 0)^2+
        algebraMap K (B K p) p*(algebraMap K (B K p) p+1) := by
  let q : MvPolynomial (Fin 4) K →+* B K p := Ideal.Quotient.mk _
  have h (i : Fin 3) : q (ThetaQuotientChart.affineEquation (equation K p) 0 i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  have h0:=h 0
  have h1:=h 1
  have h2:=h 2
  have hc (c : K) : q (MvPolynomial.C c)=algebraMap K (B K p) c := rfl
  simp [ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,equation,HpLiteralSmooth.drop_table,
    map_add,map_sub,map_mul,map_pow,map_one,map_ofNat,hc] at h0 h1 h2
  change _= _ ∧ _= _ ∧ _= _
  dsimp only [x]
  exact ⟨sub_eq_zero.mp h0,sub_eq_zero.mp h1,by linear_combination h2⟩

theorem root_sq (p : K) (hp : p ≠ 0) (i : Fin 4) :
    (x K p i)^2=HpResidueCharts.values (algebraMap K (B K p) p) (rhoB K p) i := by
  let P := algebraMap K (B K p) p
  let PI := algebraMap K (B K p) p⁻¹
  have hunit : IsUnit P := (isUnit_iff_ne_zero.mpr hp).map (algebraMap K (B K p))
  have hPPI : P*PI=1 := by dsimp [P,PI];rw [← map_mul,mul_inv_cancel₀ hp,map_one]
  obtain ⟨hV,hW,hT⟩ := relations K p
  fin_cases i
  · change (x K p 0)^2=P*rhoB K p
    dsimp [rhoB]
    change (x K p 0)^2=P*(PI*(x K p 0)^2)
    rw [← mul_assoc,hPPI,one_mul]
  · change (x K p 1)^2=2*(P-1)*(rhoB K p-1)
    apply hunit.mul_left_cancel
    change P*(x K p 1)^2=P*(2*(P-1)*(PI*(x K p 0)^2-1))
    calc
      P*(x K p 1)^2=2*(P-1)*((x K p 0)^2-P) := hV
      _=2*(P-1)*(P*PI*(x K p 0)^2-P) := by rw [hPPI,one_mul]
      _=_ := by ring
  · change (x K p 2)^2=2*(P+1)*(rhoB K p+1)
    apply hunit.mul_left_cancel
    change P*(x K p 2)^2=P*(2*(P+1)*(PI*(x K p 0)^2+1))
    calc
      P*(x K p 2)^2=2*(P+1)*((x K p 0)^2+P) := hW
      _=2*(P+1)*(P*PI*(x K p 0)^2+P) := by rw [hPPI,one_mul]
      _=_ := by ring
  · change (x K p 3)^2=(P-1)*rhoB K p+P+1
    apply hunit.mul_left_cancel
    change P*(x K p 3)^2=P*((P-1)*(PI*(x K p 0)^2)+P+1)
    calc
      P*(x K p 3)^2=(P-1)*(x K p 0)^2+P*(P+1) := hT
      _=(P-1)*(P*PI)*(x K p 0)^2+P*(P+1) := by rw [hPPI,mul_one]
      _=_ := by ring

def base (p : K) : K[X] →+* B K p := Polynomial.eval₂RingHom (algebraMap K (B K p)) (rhoB K p)

theorem base_poly (p : K) (i : Fin 4) :
    base K p (HpLiteralField.poly K p i)=HpResidueCharts.values (algebraMap K (B K p) p) (rhoB K p) i := by
  have htwo : algebraMap K (B K p) 2=2 := map_ofNat _ 2
  fin_cases i <;> simp [base,HpLiteralField.poly,HpResidueCharts.values,htwo]
  all_goals ring

def fromUniversal (p : K) (hp : p ≠ 0) : A K p →+* B K p :=
  FourRootLift08.lift K[X] (base K p) (HpLiteralField.poly K p) (x K p)
    (fun i=>(root_sq K p hp i).trans (base_poly K p i).symm)

@[simp] theorem fromUniversal_coord (p : K) (hp : p ≠ 0) (i : Fin 4) :
    fromUniversal K p hp (rootA K p i)=x K p i := FourRootLift08.lift_coord _ _ _ _ _ i
@[simp] theorem fromUniversal_base (p : K) (hp : p ≠ 0) (q : K[X]) :
    fromUniversal K p hp (algebraMap K[X] (A K p) q)=base K p q := FourRootLift08.lift_algebraMap _ _ _ _ _ q

#print axioms relations
#print axioms root_sq
#print axioms fromUniversal
end
end FourCorner.HpAffineInverse
