import ThetaCoverClassPortable.ThetaQuadraticNativeClasses

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicCurve

namespace FourCorner.ActualLocalDVRFieldOrder
variable {k L k' L' : Type} [Field k] [Field L] [Algebra k L]
  [Field k'] [Field L'] [Algebra k' L']
  (v : Place k L) (w : Place k' L') (φ : L →+* L')
  (ψ : v.toValuationSubring →+* w.toValuationSubring) [IsLocalHom ψ]
  (hcomm : ∀ a : v.toValuationSubring, φ (a:L)=(ψ a:L'))

include hcomm

/-- A genuine local map of the native DVRs gives positive integral order
scaling. The two constant fields may differ; no curve structure over the
wrong constant field is required or assumed. -/
theorem exists_positive_order_scale :
    ∃ e : ℤ,0<e ∧ ∀ f : L,w.ord (φ f)=e*v.ord f := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π:L)≠0 := by
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hφπ : φ (π:L)≠0 := by simpa only [map_zero] using φ.injective.ne hπF
  have hψπ : ψ π≠0 := by
    intro h
    exact hφπ ((hcomm π).trans (congrArg (fun a:w.toValuationSubring=>(a:L')) h))
  have hmem : ψ π ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    exact hπ.not_isUnit (IsLocalHom.map_nonunit π hu)
  have he : 0<w.ord (φ (π:L)) := by
    rw [hcomm π]
    exact (w.mem_maximalIdeal_iff_ord_pos' hψπ).mp hmem
  refine ⟨w.ord (φ (π:L)),he,?_⟩
  intro f
  by_cases hf : f=0
  · simp [hf]
  obtain ⟨u,hu⟩ := v.exists_unit_mul_zpow hf hπ
  have huF : ((u:v.toValuationSubring):L)≠0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  have hφu : φ ((u:v.toValuationSubring):L)≠0 := by simpa only [map_zero] using φ.injective.ne huF
  have huo : w.ord (φ ((u:v.toValuationSubring):L))=0 := by
    rw [hcomm]
    exact w.ord_coe_unit (Units.map ψ.toMonoidHom u)
  have hν : v.ord f=v.ord (((u:v.toValuationSubring):L)*(π:L)^(v.ord f)) :=
    congrArg v.ord hu
  conv_lhs => rw [hu,map_mul,map_zpow₀]
  rw [w.ord_mul hφu (zpow_ne_zero _ hφπ),huo,w.ord_zpow,zero_add]
  ring

/-- A single genuine order-one source function image proves the scale one;
the result then applies to every native function. -/
theorem order_eq_of_regular_positive_and_image_order_one
    (t : L) (ht : 0<v.ord t) (ht' : w.ord (φ t)=1) :
    ∀ f : L,w.ord (φ f)=v.ord f := by
  obtain ⟨e,he,heq⟩ := exists_positive_order_scale v w φ ψ hcomm
  have hm : e*v.ord t=1 := (heq t).symm.trans ht'
  have he1 : e=1 := by
    have hp : 0≤e*(v.ord t-1) := mul_nonneg (le_of_lt he) (by omega)
    have hle : e≤1 := by nlinarith
    omega
  intro f
  simpa only [he1,one_mul] using heq f

end FourCorner.ActualLocalDVRFieldOrder
