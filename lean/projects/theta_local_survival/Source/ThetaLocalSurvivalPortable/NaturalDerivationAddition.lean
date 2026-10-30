import ThetaLocalSurvivalPortable.AugmentedDerivations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.ThetaLocalSurvival.Augmented

variable {A : Type} [CommRing A] [Algebra ℚ A] (ε : A →ₐ[ℚ] ℚ)

/-- A natural binary operation on these genuine derivation spaces with
zero as two-sided unit is necessarily addition. The proof uses the two
projections and the sum map of the actual direct-sum square-zero module. -/
theorem natural_operation_is_add
    (μ : ∀ (M : Type) [AddCommGroup M] [Module ℚ M],
      augDeriv ε M → augDeriv ε M → augDeriv ε M)
    (hnat : ∀ (M N : Type) [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
      (f : M →ₗ[ℚ] N) (d e : augDeriv ε M),
      push ε f (μ M d e)=μ N (push ε f d) (push ε f e))
    (hleft : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (d : augDeriv ε M),μ M 0 d=d)
    (hright : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (d : augDeriv ε M),μ M d 0=d)
    (M : Type) [AddCommGroup M] [Module ℚ M] (d e : augDeriv ε M) : μ M d e=d+e := by
  let L : augDeriv ε (M×M) := push ε (LinearMap.inl ℚ M M) d
  let R : augDeriv ε (M×M) := push ε (LinearMap.inr ℚ M M) e
  let w : augDeriv ε (M×M) := μ (M×M) L R
  have hfl : push ε (LinearMap.fst ℚ M M) L=d := by ext a; rfl
  have hfr : push ε (LinearMap.fst ℚ M M) R=0 := by ext a; rfl
  have hsl : push ε (LinearMap.snd ℚ M M) L=0 := by ext a; rfl
  have hsr : push ε (LinearMap.snd ℚ M M) R=e := by ext a; rfl
  have hwf : push ε (LinearMap.fst ℚ M M) w=d := by
    change push ε (LinearMap.fst ℚ M M) (μ (M×M) L R)=d
    rw [hnat,hfl,hfr,hright]
  have hws : push ε (LinearMap.snd ℚ M M) w=e := by
    change push ε (LinearMap.snd ℚ M M) (μ (M×M) L R)=e
    rw [hnat,hsl,hsr,hleft]
  let sum : (M×M) →ₗ[ℚ] M := LinearMap.fst ℚ M M+LinearMap.snd ℚ M M
  have hl : push ε sum L=d := by ext a; change d a+0=d a;exact add_zero _
  have hr : push ε sum R=e := by ext a; change 0+e a=e a;exact zero_add _
  have hμ : push ε sum w=μ M d e := by
    change push ε sum (μ (M×M) L R)=μ M d e
    rw [hnat,hl,hr]
  have hsum : push ε sum w=d+e := by
    ext a
    have hf := congrArg (fun D : augDeriv ε M => D a) hwf
    have hs := congrArg (fun D : augDeriv ε M => D a) hws
    change (w a).1=d a at hf
    change (w a).2=e a at hs
    change (w a).1+(w a).2=d a+e a
    rw [hf,hs]
  exact hμ.symm.trans hsum

end FourCorner.ThetaLocalSurvival.Augmented
