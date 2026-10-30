import ThetaPairInvariants
noncomputable section
namespace FourCorner.ThetaPairGalois
open Algebra AlgebraicGeometry
open scoped TensorProduct
universe u
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : ThetaPairPresentation.Data R S)
abbrev T := S ⊗[R] S
abbrev L : S →ₐ[R] T (R:=R) (S:=S) := Algebra.TensorProduct.includeLeft
abbrev N : S →ₐ[R] T (R:=R) (S:=S) := Algebra.TensorProduct.includeRight
abbrev sig := ThetaPairInvariants.negate P
def phi : T (R:=R) (S:=S) →ₐ[R] S×S :=
  Algebra.TensorProduct.lift ((AlgHom.id R S).prod (AlgHom.id R S))
    ((AlgHom.id R S).prod (sig P)) (fun _ _=>Commute.all _ _)
lemma phi_tmul (x y : S) : phi P (x ⊗ₜ[R] y)=(x*y,x*sig P y) := by
  simp [phi,Algebra.TensorProduct.lift_tmul]
lemma phi_L (x : S) : phi P (L x)=(x,x) := by
  change phi P (x ⊗ₜ[R] (1:S))=(x,x)
  rw [phi_tmul]
  simp
lemma phi_N (x : S) : phi P (N x)=(x,sig P x) := by
  change phi P ((1:S) ⊗ₜ[R] x)=(x,sig P x)
  rw [phi_tmul]
  simp
lemma left_right_mul (x y : S) : L x*N y=x ⊗ₜ[R] y := by
  change (x ⊗ₜ[R] (1:S))*((1:S) ⊗ₜ[R] y)=x ⊗ₜ[R] y
  simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
lemma norm (ell : R) (h : P.a+ell*P.b=1) :
    P.u^2+algebraMap R S ell*P.v^2=1 := by
  rw [P.u_sq,P.v_sq,←map_mul,←map_add,h,map_one]
def d (ell : R) : T (R:=R) (S:=S) := L P.u*N P.u+algebraMap R (T (R:=R) (S:=S)) ell*(L P.v*N P.v)
lemma left_u_d (ell : R) (h : P.a+ell*P.b=1) : L P.u*d P ell=N P.u := by
  have hlu:=congrArg (L (R:=R) (S:=S)) P.u_sq
  have hnu:=congrArg (N (R:=R) (S:=S)) P.u_sq
  have hlc:=congrArg (L (R:=R) (S:=S)) P.uv
  have hnc:=congrArg (N (R:=R) (S:=S)) P.uv
  have hn:=congrArg (N (R:=R) (S:=S)) (norm P ell h)
  simp only [map_add,map_mul,map_pow,map_one,AlgHom.commutes] at hlu hnu hlc hnc hn
  unfold d
  linear_combination N P.u*(hlu-hnu)+algebraMap R (T (R:=R) (S:=S)) ell*N P.v*(hlc-hnc)+N P.u*hn
lemma left_v_d (ell : R) (h : P.a+ell*P.b=1) : L P.v*d P ell=N P.v := by
  have hlv:=congrArg (L (R:=R) (S:=S)) P.v_sq
  have hnv:=congrArg (N (R:=R) (S:=S)) P.v_sq
  have hlc:=congrArg (L (R:=R) (S:=S)) P.uv
  have hnc:=congrArg (N (R:=R) (S:=S)) P.uv
  have hn:=congrArg (N (R:=R) (S:=S)) (norm P ell h)
  simp only [map_add,map_mul,map_pow,map_one,AlgHom.commutes] at hlv hnv hlc hnc hn
  unfold d
  linear_combination N P.u*(hlc-hnc)+algebraMap R (T (R:=R) (S:=S)) ell*N P.v*(hlv-hnv)+N P.v*hn

def half (h2 : IsUnit (2:R)) : R := ↑h2.unit⁻¹
lemma half_two (h2 : IsUnit (2:R)) : (2:R)*half h2=1 := h2.mul_val_inv
def e (ell : R) (h2 : IsUnit (2:R)) : T (R:=R) (S:=S) := algebraMap R (T (R:=R) (S:=S)) (half h2)*(1+d P ell)
lemma twice_e (ell : R) (h2 : IsUnit (2:R)) : 2*e P ell h2-1=d P ell := by
  have hh:=congrArg (algebraMap R (T (R:=R) (S:=S))) (half_two h2)
  simp only [map_mul,map_ofNat,map_one] at hh
  unfold e
  linear_combination (1+d P ell)*hh
lemma phi_d (ell : R) (h : P.a+ell*P.b=1) : phi P (d P ell)=(1,-1) := by
  simp only [d,map_add,map_mul,phi_L,phi_N,AlgHom.commutes]
  apply Prod.ext
  · change P.u*P.u+algebraMap R S ell*(P.v*P.v)=1
    simpa only [pow_two] using norm P ell h
  · change P.u*sig P P.u+algebraMap R S ell*(P.v*sig P P.v)= -1
    rw [ThetaPairInvariants.negate_u,ThetaPairInvariants.negate_v]
    linear_combination -norm P ell h
lemma phi_e (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) : phi P (e P ell h2)=(1,0) := by
  rw [e,map_mul,map_add,map_one,phi_d P ell h]
  rw [AlgHom.commutes]
  apply Prod.ext
  · change algebraMap R S (half h2)*(1+1)=1
    have hh:=congrArg (algebraMap R S) (half_two h2)
    simp only [map_mul,map_ofNat,map_one] at hh
    linear_combination hh
  · change algebraMap R S (half h2)*(1+ -1)=0
    ring

def psi (ell : R) (h2 : IsUnit (2:R)) (p : S×S) : T (R:=R) (S:=S) :=
  L p.1*e P ell h2+L p.2*(1-e P ell h2)
lemma psi_add (ell : R) (h2 : IsUnit (2:R)) (p q : S×S) :
    psi P ell h2 (p+q)=psi P ell h2 p+psi P ell h2 q := by
  simp only [psi,Prod.fst_add,Prod.snd_add,map_add]
  ring
lemma reconstruction (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) (y : S) :
    psi P ell h2 (y,sig P y)=N y := by
  obtain ⟨a,b,c,hy⟩:=ThetaPairInvariants.normal_form P y
  have hsig : sig P y=algebraMap R S a-algebraMap R S b*P.u-algebraMap R S c*P.v := by
    rw [hy,map_add,map_add,map_mul,map_mul,ThetaPairInvariants.negate_u,ThetaPairInvariants.negate_v]
    simp only [AlgHom.commutes]
    ring
  have hly:=congrArg (L (R:=R) (S:=S)) hy
  have hny:=congrArg (N (R:=R) (S:=S)) hy
  have hls:=congrArg (L (R:=R) (S:=S)) hsig
  simp only [map_add,map_sub,map_mul,AlgHom.commutes] at hly hny hls
  have hu : L P.u*(2*e P ell h2-1)=N P.u := by rw [twice_e];exact left_u_d P ell h
  have hv : L P.v*(2*e P ell h2-1)=N P.v := by rw [twice_e];exact left_v_d P ell h
  change L y*e P ell h2+L (sig P y)*(1-e P ell h2)=N y
  rw [hly,hls,hny]
  linear_combination algebraMap R (T (R:=R) (S:=S)) b*hu+algebraMap R (T (R:=R) (S:=S)) c*hv
lemma psi_phi_tmul (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) (x y : S) :
    psi P ell h2 (phi P (x ⊗ₜ[R] y))=x ⊗ₜ[R] y := by
  rw [phi_tmul,←left_right_mul x y]
  change L (x*y)*e P ell h2+L (x*sig P y)*(1-e P ell h2)=L x*N y
  rw [map_mul,map_mul]
  have hr:=reconstruction P ell h h2 y
  change L y*e P ell h2+L (sig P y)*(1-e P ell h2)=N y at hr
  linear_combination L x*hr
lemma psi_phi (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) (z : T (R:=R) (S:=S)) :
    psi P ell h2 (phi P z)=z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [psi]
  | add z w hz hw => rw [map_add,psi_add,hz,hw]
  | tmul x y => exact psi_phi_tmul P ell h h2 x y
lemma phi_psi (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) (p : S×S) :
    phi P (psi P ell h2 p)=p := by
  rw [psi,map_add,map_mul,map_mul,phi_L,phi_L,map_sub,map_one,phi_e P ell h h2]
  apply Prod.ext <;> simp
/-- The actual kernel-pair algebra is the disjoint union of the identity and sign graphs. -/
def equiv (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) : T (R:=R) (S:=S) ≃ₐ[R] S×S :=
  AlgEquiv.ofBijective (phi P) ⟨fun z w hzw=>by
    have hh:=congrArg (psi P ell h2) hzw
    simpa only [psi_phi P ell h h2] using hh,
    fun p=>⟨psi P ell h2 p,phi_psi P ell h h2 p⟩⟩
end FourCorner.ThetaPairGalois
#print axioms FourCorner.ThetaPairGalois.equiv
