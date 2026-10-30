import ThetaCoverClassPortable.ActualProjectiveSquareZeroLift
import Mathlib.LinearAlgebra.TensorProduct.Tower
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorProduct
universe u
namespace Module
/-- Actual field-fibre ranks are unchanged by a square-zero quotient and its
specified ring equivalence. No finite/free/Noetherian hypothesis is needed. -/
theorem finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
    {R S:Type u}[CommRing R][CommRing S](I:Ideal R)(hI:I^2=⊥)(φ:R⧸I≃+*S)
    (P:Type u)[AddCommGroup P][Module S P]
    (P':Type u)[AddCommGroup P'][Module R P']{n:ℕ}
    (hr:∀(K:Type u)[Field K][Algebra S K],Module.finrank K (K⊗[S]P)=n)
    (e: letI : Module (R⧸I) P := Module.compHom P φ.toRingHom;
      (R⧸I)⊗[R]P' ≃ₗ[R⧸I]P) :
    ∀(K:Type u)[Field K][Algebra R K],Module.finrank K (K⊗[R]P')=n := by
  intro K _ _
  have hk : I ≤ RingHom.ker (algebraMap R K) := by
    intro x hx
    have hh : x^2=0 := by
      have hmem:=Ideal.pow_mem_pow hx 2
      rw [hI] at hmem
      exact hmem
    change algebraMap R K x=0
    have h2 : (algebraMap R K x)^2=0 := by rw [←map_pow,hh,map_zero]
    exact (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp h2
  let ψ : R⧸I→+*K := Ideal.Quotient.lift I (algebraMap R K) hk
  letI : Algebra (R⧸I) K := ψ.toAlgebra
  letI : IsScalarTower R (R⧸I) K := IsScalarTower.of_algebraMap_eq' (by ext x;rfl)
  letI : Algebra S K := (ψ.comp φ.symm.toRingHom).toAlgebra
  letI : Module (R⧸I) P := Module.compHom P φ.toRingHom
  have hK (r:R⧸I)(x:K) : (φ r) • x = r • x := by
    change ψ (φ.symm (φ r))*x=ψ r*x
    rw [φ.symm_apply_apply]
  letI : CompatibleSMul (R⧸I) S K P := ⟨fun s x p=>by
    obtain ⟨r,rfl⟩:=φ.surjective s
    rw [hK]
    exact TensorProduct.smul_tmul r x p⟩
  letI : CompatibleSMul S (R⧸I) K P := ⟨fun r x p=>by
    rw [←hK]
    exact TensorProduct.smul_tmul (φ r) x p⟩
  let a := (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R⧸I) K K P').symm
  let b := LinearEquiv.baseChange (R⧸I) K _ _ e
  let c := TensorProduct.equivOfCompatibleSMul S (R⧸I) K K P
  exact ((a.trans b).trans c).finrank_eq.trans (hr K)
#print axioms finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
end Module
