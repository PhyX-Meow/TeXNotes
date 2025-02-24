#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  numbering: "1.1.",
)

#title[
  *Notes of Siu-Yau*
]

= The idea

The goal of the paper is to prove the following #emph[Frankel conjecture]:
#theorem(name: "Siu-Yau")[
  Every compact Kähler manifold of positive bisectional curvature is bi-holomorphic
  to the complex projective space.
] <main-thm>

To achieve this, we stand on the shoulder of giants:
#theorem(name: "Bishop-Goldberg")[
  The second Betti number of a compact Kähler manifold $M$ of positive bisectional
  curvature is 1.
]
#theorem(name: "Kobayashi-Ochiai")[
  If $M$ is a compact complex manifold with ample line bundle $L$, suppose $
    c_1(M)>=(m+1)c_1(L)
  . $ Then $M$ is bi-holomorphic to $CC PP^n$.
]

#let bt = bar(math.partial)
#let ii = math.sqrt($-1$)

= Relation of energy and $bt$-energy
Consider map $f:M->N$ between Kähler manifolds with Kähler metric $
  omega_M=sqrt(-1)g_(i bar(j))dd(z^i)wed dd(bar(z)^j), quad
  omega_N=sqrt(-1)h_(alpha bar(beta))dd(z^alpha)wed dd(bar(z)^beta)
. $ Define the pointwise energy of $f$ be $
  e(f)=abs(dd(f))^2=abs(pt f)^2+lr(abs(bt f),size:#12pt)^2
. $ And the pointwise $bt$-energy be $
  |bt f|^2=g^(bar(i)j)f_bar(i)^alpha ov(f_bar(j)^beta)h_(alpha bar(beta))
  =g^(bar(i)j)pdv(f^alpha,bar(z)^i) ov(pdv(f^beta,bar(z)^j))h_(alpha bar(beta))
. $ Suppose $dim_CC M=1$, the pull-back of the Kähler form on $N$ by $f$ is $
  ii h_(alpha bar(beta))dd(f^alpha)wed dd(bar(f)^beta)
  =ii h_(alpha bar(beta))lr((pt f^alpha ov(pt f^beta)-bt f^alpha ov(bt f^beta)),size:#14pt)dd(z)wed dd(bar(z))
. $ Hence $
  int_M abs(pt f)^2-int_M lr(abs(bt f),size:#12pt)^2=int_M ii h_(alpha bar(beta))dd(f^alpha)wed dd(ov(f^beta))
, $ which is equal to the Kähler form of $N$ evaluated at the push-forward homology class of $M$ by $f$. So $
  int_M abs(pt f)^2=1/2 E(f)+1/2 omega_N [f_* M], quad 
  int_M lr(abs(bt f),size:#12pt)^2=1/2 E(f)-1/2 omega_N [f_* M]
. $ Thus the energy-minimizing maps are precisely the same as $bt$-energy minimizing maps.

= Second variation formula
Suppose $f_t$ is a family of smooth maps for $t in D(0,eps)cc CC$. The goal is to compute $pdv(,t,bar(t))
|bt f|^2$. Use normal coordinate at $p in M$ and $q=f(p)in N$, we have $
  dd(g_(i bar(j)))=0 "at" P, quad dd(h_(alpha bar(beta)))=0 "and"
  pt_gamma pt_delta h_(alpha bar(beta))=0 "at" Q
. $ Then at $p$, $
  pdv(,t,bar(t))|bt f|^2&=pt_t bt_t (g^(bar(i)j)f_bar(i)^alpha ov(f_bar(j)^beta)h_(alpha bar(beta))) \
  &=2Re g^(bar(i)j)(pt_t bt_t f_(bar(i))^alpha)ov(f_(bar(j))^beta)h_(alpha bar(beta))
  +g^(bar(i)j)pt_t f_(bar(i))^alpha ov(pt_t f_(bar(j))^beta)h_(alpha bar(beta))
  +g^(bar(i)j)bt_t f_(bar(i))^alpha ov(bt_t f_(bar(j))^beta)h_(alpha bar(beta)) \
  &#hide[=]
  +g^(bar(i)j)f_bar(i)^alpha ov(f_bar(j)^beta)pt_mu pt_bar(nu)h_(alpha bar(beta))pt_t f^mu ov(pt_t f^nu)
  +g^(bar(i)j)f_bar(i)^alpha ov(f_bar(j)^beta)pt_mu pt_bar(nu)h_(alpha bar(beta))bt_t f^mu ov(bt_t f^nu)
. $ Consider the vector field on $M$ defined by $
  xi^bar(i)=g^(bar(i)j)(nd_t nd_(bar(t))f^alpha)ov(f_bar(j)^beta)h_(alpha bar(beta)), quad
  "where" nd_t nd_(bar(t))f^alpha=pt_t bt_t f^alpha+Gamma_(beta gamma)^alpha pt_t f^beta bt_t f^gamma
. $ Then the divergence of $xi^(bar(i))$ at $p$ is $
  nd_(bar(i))xi^(bar(i))&=g^(bar(i)j)nd_bar(i)nd_t nd_bar(t)f^alpha ov(f_bar(j)^beta) h_(alpha bar(beta))
  +g^(bar(i)j)nd^2_(t bar(t))f^alpha ov(nd_i f_(bar(j))^beta) h_(alpha bar(beta)) \
  &=g^(bar(i)j)(nd^2_(t bar(t))f_bar(i)^alpha) ov(f_bar(j)^beta) h_(alpha bar(beta))
  +nd^2_(t bar(t))f^alpha ov(lap_g f^beta) h_(alpha bar(beta))
  +g^(bar(i)j)R_(bar(i)t gamma)#[]^alpha bt_t f^gamma ov(f_bar(j)^beta) h_(alpha bar(beta)) \
  &=g^(bar(i)j)(nd^2_(t bar(t))f_bar(i)^alpha) ov(f_bar(j)^beta) h_(alpha bar(beta))
  +nd^2_(t bar(t))f^alpha ov(lap_g f^beta) h_(alpha bar(beta)) \
  &#hide[=]-g^(bar(i)j)R_(mu bar(nu)alpha bar(beta)) pt_t f^mu ov(f_i^nu) bt_t f^alpha ov(f_bar(j)^beta)
  +g^(bar(i)j)R_(mu bar(nu)alpha bar(beta))f_bar(i)^mu ov(bt_t f^nu)bt_t f^alpha ov(f_bar(j)^beta)
. $ Note that the last term is real, and equal to $
  g^(bar(i)j)R_(mu bar(nu)alpha bar(beta))bt_t f^mu ov(bt_t f^nu) f_bar(i)^alpha ov(f_bar(j)^beta)
. $ Now assume $f$ is harmonic at $t=0$, #ie $lap_g f^alpha=0$, then at $t=0$, $
  pdv(,t,bar(t))|bt f|^2-2 Re div xi
  =&g^(bar(i)j)nd_t f_(bar(i))^alpha ov(nd_t f_(bar(j))^beta)h_(alpha bar(beta))
  +g^(bar(i)j)nd_bar(t) f_(bar(i))^alpha ov(nd_bar(t) f_(bar(j))^beta)h_(alpha bar(beta)) \
  &-g^(bar(i)j)R_(mu bar(nu)alpha bar(beta))pt_t f^mu ov(pt_t f^nu)f_bar(i)^alpha ov(f_bar(j)^beta)
  -3g^(bar(i)j)R_(mu bar(nu)alpha bar(beta))bt_t f^mu ov(bt_t f^nu)f_bar(i)^alpha ov(f_bar(j)^beta) \
  &+2Re g^(bar(i)j)R_(mu bar(nu)alpha bar(beta)) pt_t f^mu ov(f_i^nu) bt_t f^alpha ov(f_bar(j)^beta)
. $ Integrate over $M$ we get $
  lr(pdv(,t,bar(t))|)_(t=0)int_M |bt f|^2 dd(V_g)=int_M "RHS"
. $ 

= Analyticity of minimizer
Suppose $N$ is compact Kähler with positive holomorphic bisectional curvature (HBSC). Let $f$ be an
energy-minimizing map $PP^1->N$.
#proposition[
  If $f^* c_1(N)$ is $>=0$, then $f$ is holomorphic ($<=0=>$ anti-holomorphic).
]
#proof[
  Let $T N=T^(1,0)N$ be the holomorphic tangent bundle of $N$ and $z$ be a local complex coordinate on $PP^1$.
  Let $cal(F)$ be the sheaf of germs of local holomorphic sections of $f^* T N$. We claim that $cal(F)$ is
  locally free and the associated holomorphic vector bundle is isomorphic to $f^* T N$. (Note that a priori
  $f^* T N$ may not be holomorphic since $f$ may not be). Only need to show for any $p in PP^1$ there exists
  local holomorphic sections $s_1,...,s_m$ that are $CC$-linearly independent at $p$.
  
  Choose local normal coordinate $z$ at $p$ and $w^alpha$ at $q=f(p)$, then every section is of of form $
    s=s^alpha pdv(,w^alpha)
  , $ and since $nd_bar(z)pdv(,w^alpha)=0$ in normal coordinate $
    nd_bar(z)s=pdv(s^alpha,bar(z))pdv(,w^alpha)
  . $ Choose smooth sections $v_i,i=1,...,m$ of $f^* T M$ at $p$, such that $v_i^alpha$ is holomorphic in 
  variable $z$ and the matrix $(v_i^alpha (p))_(m times m)$ is non-singular at $p$. Consider equation $
    nd_bar(z)u_i=pdv(u_i^alpha,bar(z))+Gamma_(beta gamma)^alpha f_bar(z)^beta u_i^gamma=1/z nd_bar(z)v_i
  , $ Then $
    u_i^alpha (z)=1/(2pi ii)int_CC 1/(z-zeta)(1/zeta (nd_bar(z)v_i)(zeta)-Gamma_(beta gamma)^alpha (f(zeta))
    f_(bar(z))^beta (zeta) u_i^gamma (zeta)) dd(z)wed dd(bar(z))
  . $ Now take $
    s_i=v_i-z u_i
  , $ we see $nd_bar(z)s_i=0$ and $s_i (p)=v_i (p)$ form a $CC$-basis.

  Now $f^* T M$ is a holomorphic vector bundle. By the theorem of Grothendieck, $
    f^* T=L_1 dsum dots.c dsum L_m
  . $ Since $f^* c_1>=0$, there is at least one $c_1 (L_i)>=0$. Riemann-Roch shows that there is a non-trivial
  global holomorphic section $s$ of this $L_i$. Consider family of maps $
    f_t:PP^1-->N,quad bt_t f_t^alpha=0,pt_t f_t^alpha=s^alpha
  . $ Since $s$ is a holomorphic section, we have $
    nd_t nd_bar(z)f^alpha=nd_bar(z)s^alpha=0,quad nd_bar(t)nd_bar(z)f^alpha=nd_bar(z)\(bt_t f^alpha\)=0
  . $ By the 2nd variation formula, we have $
    0<=pdv(,t,bar(t))int_(PP^1)|bt f|^2=-int_(PP^1)R_(mu bar(nu)alpha bar(beta))pt_t f^mu ov(pt_t f^nu)
    f_bar(z)^alpha ov(f_bar(z)^beta)ii dd(z)wed dd(bar(z))
  . $ Since the HBSC of $N$ is positive, $"RHS">=0$. It follows that $bt f^alpha=0$ outside the zero set of 
  $s^alpha=pt_t f^alpha$. Thus $f$ is holomorphic since $Z(s^alpha)$ is finite.
]

= Existence of minimizer
#proposition[
  For every $C^1$ map $F:SS^2->N$ there exists finitely many energy-minimizing maps $f_i:SS^2->N$ such that $
    sum_i [f_i]=[F] quad "and" quad tilde(E)([F])=sum_i E(f_i)
  . $ Where $tilde(E)([F])$ is defined to be the infimum of sum of the energies of maps sum to $[F]$.
]
#proof[
  By Sacks-Uhlenbeck, there is a constant $c>0$ that any non-trivial harmonic map and homotopically non-trivial
  $C^1$ map $SS^2->N$ has energy $>c$. Let $k$ be the smallest integer with $E(f)<= (k c)/2$
]

= Holomorphic deformation of rational curves
