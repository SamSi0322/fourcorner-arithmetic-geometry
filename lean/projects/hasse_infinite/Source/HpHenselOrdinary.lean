import HpResidueCharts
import FourCorner.HasseNorms
import PadicUnitNeighbourhood
import TranscendentalParameters

namespace FourCorner.HpHenselOrdinary

open HpResidueCharts HasseNorms PadicUnitNeighbourhood
noncomputable section

def toLocalPoint {K : Type*} [Field K] [CharZero K] (p : ℚ) (e : K)
    (he : Transcendental ℚ e) (r : Fin 4 → K)
    (hr0 : ∀i,r i ≠ 0) (hrs : ∀i,r i^2=values (p : K) e i) : LocalPoint K (p : K) where
  rho := e
  u := r 0
  v := r 1
  w := r 2
  t := r 3
  rho_ne_zero := by intro h;apply he;rw [h];exact isAlgebraic_zero
  rho_ne_one := by intro h;apply he;rw [h];exact isAlgebraic_one
  rho_ne_neg_one := by
    intro h
    apply he
    rw [h]
    simpa only [map_neg,map_one] using (isAlgebraic_algebraMap (R:=ℚ) (A:=K) (-1 : ℚ))
  u_ne_zero := hr0 0
  v_ne_zero := hr0 1
  w_ne_zero := hr0 2
  t_ne_zero := hr0 3
  sqU := hrs 0
  sqV := hrs 1
  sqW := hrs 2
  sqT := hrs 3

variable {q : ℕ} [Fact q.Prime]

theorem continuous_values (p : ℚ_[q]) (i : Fin 4) : Continuous (fun e : ℚ_[q] => values p e i) := by
  fin_cases i <;> simp only [values] <;> fun_prop

/-- Four nonzero residue roots lift simultaneously at a genuine
Q-transcendental parameter, with every original source guard proved. -/
theorem ordinary (hq : q ≠ 2) (p : ℚ) (P A : ℤ_[q]) (hP : (P : ℚ_[q])=(p : ℚ_[q]))
    (r0 : Fin 4 → ZMod q)
    (hr0 : ∀i,r0 i^2=values (PadicInt.toZMod P) (PadicInt.toZMod A) i)
    (hn : ∀i,r0 i ≠ 0) :
    ∃ S : LocalPoint ℚ_[q] (p : ℚ_[q]),Transcendental ℚ S.rho := by
  let f (i : Fin 4) (e : ℚ_[q]) := values (p : ℚ_[q]) e i
  let a (i : Fin 4) := values P A i
  have ha (i : Fin 4) : PadicInt.toZMod (a i)=r0 i^2 :=
    (map_values PadicInt.toZMod P A i).trans (hr0 i).symm
  obtain ⟨e,he,hr⟩ := transcendental_simultaneous_roots hq f A a
    (fun i => (continuous_values _ i).continuousAt)
    (fun i => by
      have hTwo : ((2 : ℤ_[q]) : ℚ_[q])=(2 : ℚ_[q]) := rfl
      fin_cases i <;> simp only [f,a,values,PadicInt.coe_mul,PadicInt.coe_add,
        PadicInt.coe_sub,PadicInt.coe_one,hTwo,hP])
    (fun i => by rw [ha];exact pow_ne_zero _ (hn i))
    (fun i => by rw [ha];exact IsSquare.sq _)
  choose r hr0' hrs using hr
  exact ⟨toLocalPoint p e he r hr0' hrs,he⟩

#print axioms toLocalPoint
#print axioms ordinary

end
end FourCorner.HpHenselOrdinary
