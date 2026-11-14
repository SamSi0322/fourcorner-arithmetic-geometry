"""Exact symbolic checks for the new manuscript sections; no point search."""
from pathlib import Path
import json
from fractions import Fraction
import sympy as s

checks = {}


def zero(name, expression):
    value = s.factor(expression)
    assert value == 0, (name, value)
    checks[name] = True


h, k, W = s.symbols("h k W")
phi = lambda z: z**4 - 6*z**2 + 1
A = (1+h*h)*(1+k*k)
T = A+W
N = [1-h-k-h*k, 1-h+k+h*k, 1+h-k+h*k, 1+h+k-h*k]
X = T/2-2*k*(1-h*h)
Y = T/2-2*h*(1-k*k)
relation = s.Poly(W*W-phi(h)*phi(k), W)
for j, (cx, cy) in enumerate([(0,0),(1,0),(0,1),(1,1)]):
    expr = s.expand((X-cx*T)**2+(Y-cy*T)**2-N[j]**2*T)
    zero(f"symmetric_return_{j}", s.Poly(expr,W).rem(relation).as_expr())
zero("symmetric_discriminant", A*A-phi(h)*phi(k)-8*(k*k*(1-h*h)**2+h*h*(1-k*k)**2))

r0,r1,r2,r3 = r = s.symbols("r0 r1 r2 r3")
total=sum(r)
hh=(r2+r3-r0-r1)/total
kk=(r1+r3-r0-r2)/total
flag=s.Poly(r0*r0+r3*r3-r1*r1-r2*r2,r3)
for j in range(4):
    polynomial=s.cancel(total*total*N[j].subs({h:hh,k:kk})-4*r[j]*total)
    zero(f"positive_distance_converse_{j}",s.Poly(polynomial,r3).rem(flag).as_expr())

u,v=s.symbols("u v")
S2=2*u*(v+1)/(u+v)
D2=2*(v-1)/(u+v)
Sig2=2*v*(u+1)/(u+v)
Del2=2*(u-1)/(u+v)
t=(u*v+1)/(u+v)
zero("source_flag",S2+D2-Sig2-Del2)
zero("source_metric",(S2-2)*(2-D2)-Sig2*Del2)
zero("source_sigma",(Sig2-2)/D2-u)
zero("source_sigma_prime",(S2-2)/Del2-v)
zero("source_kernel_sigma",u*(u*u-1)-(t*t-1)*S2*(u+v)**2/(D2*(v+1)**2))
zero("source_kernel_sigma_prime",v*(v*v-1)-(t*t-1)*Sig2*(u+v)**2/(Del2*(u+1)**2))
zero("source_last_square",2*(u-1)*(u+v)-Del2*(u+v)**2)

ell,M,S,Z,mu,ss=s.symbols("ell M S Z mu ss")
aa=1+ell**2
dd=(ell**2-1)**2
bb=ell**4-10*ell**2+1
conic=2*S*S-2*aa*S*(M+Z)+dd*(M*M+Z*Z)-2*bb*M*Z
matrix=s.Matrix([[2,-aa,-aa],[-aa,dd,-bb],[-aa,-bb,dd]])
zero("quartic_conic_determinant",matrix.det()+4*phi(ell)**2)
zero("quartic_conic_axis_M",s.discriminant(conic.subs(M,0).subs(Z,1),S)+4*phi(ell))
zero("quartic_conic_axis_S",s.discriminant(conic.subs(S,0).subs(Z,1),M)+64*ell**2*phi(ell))
F=(2*ss*ss-aa*(1+mu*mu))**2+phi(ell)*phi(mu)
zero("quartic_conic_relation",F-2*conic.subs({S:ss*ss,M:mu*mu,Z:1}))
XX=ss*ss/2+2*ell*mu
YY=ss*ss/2-(ell*ell-1)*(mu*mu-1)/2
RR=[ell+mu,mu-ell,ell*mu+1,ell*mu-1]
for j,(cx,cy) in enumerate([(0,0),(1,0),(0,1),(1,1)]):
    zero(f"quartic_same_point_return_{j}",s.expand((XX-cx*ss*ss)**2+(YY-cy*ss*ss)**2-RR[j]**2*ss*ss-F/8))
ell_y=dd*mu*mu-bb-aa*ss*ss
zero("elliptic_quotient_identity",s.Poly(s.expand(ell_y**2+phi(ell)*(ss*ss-4)*(ss*ss-4*ell*ell)),mu).rem(s.Poly(F,mu)).as_expr())

# The first genus-one quotient maps to E'_c; a rational 2-isogeny
# from E'_c followed by a change of coordinates gives E_c.
c,z,w,x,y=s.symbols("c z w x y")
xp=c*z*z;yp=c*z*w
zero("quartic_to_elliptic_prime",s.Poly(s.expand(yp*yp-(xp**3-6*c*xp*xp+c*c*xp)),w).rem(s.Poly(w*w-c*phi(z),w)).as_expr())
xx=(x*x-6*c*x+c*c)/x
yy=y*(1-c*c/x**2)
isog=s.together(yy*yy-xx*(xx+4*c)*(xx+8*c))
num=s.fraction(isog)[0]
zero("two_isogeny",s.Poly(num,y).rem(s.Poly(y*y-x*(x*x-6*c*x+c*c),y)).as_expr())
zero("elliptic_shift",(4*(z-c))*(4*z)*(4*(z+c))-64*z*(z*z-c*c))

# Exact identities governing the eight signed sums.
G,L,MX,MY=s.symbols("G L MX MY")
P=r0*r3-r1*r2;Q=r0*r3+r1*r2
sigma_a=r0+r1-r2-r3
sigma_b=r0-r1+r2-r3
sigma_c=r0-r1-r2+r3
zero("sigma_1_c",s.Poly(total*sigma_c-2*P,r3).rem(flag).as_expr())
zero("sigma_a_b",s.Poly(sigma_a*sigma_b+2*P,r3).rem(flag).as_expr())
zero("sigma_o0_o3",s.Poly((total-2*r0)*(total-2*r3)-2*Q,r3).rem(flag).as_expr())
zero("sigma_o1_o2",s.Poly((total-2*r1)*(total-2*r2)-2*Q,r3).rem(flag).as_expr())

xx,yy=s.symbols("xx yy")
R=[xx*xx+yy*yy,(xx-L)**2+yy*yy,xx*xx+(yy-L)**2,(xx-L)**2+(yy-L)**2]
zero("P_times_Q",R[0]*R[3]-R[1]*R[2]+L*L*(L-2*xx)*(L-2*yy))

# The independent scale counterexample must remain a nonsquare after repair.
pq=[Fraction(t) for t in (17,1,8,15)]
qq=[Fraction(t) for t in (689,31,400,561)]
def invariant(p,q):
    return 4*(p[0]*q[0]+161*p[1]*q[1])/((p[0]+p[3])*(q[0]+q[3]))
assert invariant(pq,qq)==invariant([x/Fraction(16704) for x in pq],qq)==Fraction(1044,625)
checks["scale_counterexample_repaired"]=True

result={"status":"PASS_EXACT_SYMBOLIC_IDENTITIES","checks":checks,
        "scope":"Algebraic identities only. Genus, group, valuation, rank and global assertions also require the written proofs."}
out=Path(__file__).with_name("EXACT_NEW_MATHEMATICS_CHECK.json")
out.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"status":result["status"],"checks":len(checks)},indent=2))
