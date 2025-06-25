#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  heading-font: "",
  numbering: none,
)

#import "@preview/touying:0.6.1": *
#import themes.university: *
#show: university-theme.with(
  aspect-ratio: "4-3",
  config-info(
    title: [Stability of minimal submanifolds],
    author: text(font: "LXGW WenKai", weight:400)[薛皓天],
    date: datetime.today(),
    institution: [Stanford University],
  ),
)

#title-slide()

== Minimality and stability
#slide[
#strong[Setup:] $(M^(n+k),g)$ be a Riemannian manifold, $F:Sigma^n->M$ be an smooth immersed submanifold with
smooth boundary.

We could define the _2nd fundamental form_ of $Sigma$ by $
  II^Sigma (X,Y)=nd^M_(X)Y-nd^Sigma_X Y=\(nd^M_X Y\)^perp
, $ for any $X,Y$ smooth vector fields on $Sigma$. And the _mean curvature_ $
  H=tr_Sigma II=sum_i \(nd^M_(e_i) e_i\)^perp quad "for" {e_i} "o.n.b of" T_p Sigma
. $ Roughly speaking, $II$ measures how $Sigma$ curves in ambient space, and $H$ is the average direction that 
$Sigma$ curves to.

For example, the mean curvature of a round sphere in $RR^(n+1)$ of radius $R$ is the inward
normal with length $n\/R$.

Consider a smooth family of maps $F_t:Sigma times (-eps,eps)->M$ with $F_0=F$ and $F_t$ only differ from $F$
on a compact set in $Sigma\\pt Sigma$. Let $X=lr(dv(,t)|)_(t=0)F_t$ be the variation field, then the 1st
variation of area is given by $
    lr(dv(,t)|,size:#48pt)_(t=0)cal(A)(Sigma_t)=int_Sigma div_Sigma X dd(mu_Sigma)
    =int_(pt Sigma)X dot.c nu_(pt Sigma) dd(mu_(pt Sigma))-int_Sigma X dot.c H dd(mu_Sigma)
, $ where $H$ is the mean curvature of $Sigma$, defined by #v(-4pt) $
  H=tr_Sigma (II), quad "and" quad II(X,Y)=nd^M_(X)Y-nd^Sigma_X Y
. $ #v(-4pt) $H$ can be understood as the average direction where $Sigma$ curves.
$Sigma$ is said to be _minimal_ or _stationary_ if the 1st variation is 0 for any smooth variations,
which is true if and only if $H=0$.

If we want to know whether $Sigma$ actually minimizes area (at least locally), we need to calculate the 2nd 
variation. Suppose $Sigma$ is minimal, #ie $H=0$, then $
  I(X,X):&=lr(dv(#[]^2,t^2)|,size:#48pt)_(t=0)op("Area")(Sigma_t) \
  &=int_Sigma |\(hat(nd) X\)^perp|^2+(div_Sigma X)^2-sum_(i,j=1)^n pari(nd_i X,e_j)pari(nd_j X,e_i) \
  &#hide[$=int_Sigma$]-sum_(i=1)^n R(X,e_i,e_i,X) dd(mu_Sigma)
. $ $Sigma$ is said to be _stable_ if $I(X,X)>=0$ for any smooth vector field $X$ supported on a compact set 
away from boundary.

#pagebreak()
Up to diffeomorphism, we can change the parameter to make the variation field $X$ a normal field to $Sigma$.
In this case $
  I(X,X)=int_Sigma |\(hat(nd) X\)^perp|^2-|X dot.c II^Sigma (dot.c,dot.c)|^2
  -sum_(i=1)^n R(X,e_i,e_i,X) dd(mu_Sigma)
. $ When the ambient space is $RR^(n+k)$, there is no curvature term since Euclidean spaces are flat.
#example(numbering:none)[
  Plane $RR^2 cc RR^3$ is stable, since it is totally geodesic.
  #v(-8pt)
  #figure(image("figures/R2.svg", width: 50%))
]
#pagebreak()
#example(numbering:none)[
  Helicoid, Catenoid in $RR^3$ are unstable.
  #v(-1em)
  #figure(
    grid(
      columns: 2,
      gutter: 0pt,
      image("figures/helicoid.svg", width: 100%),
      image("figures/catenoid.svg", width: 100%),
    ),
  ) #v(-1em)
]
#proposition(numbering:none)[
  If a smooth minimal surface $Sigma^n->RR^(n+1)$ is stable, then its universal cover $tilde(Sigma)->
  RR^(n+1)$ is also stable.
]
With this we can assume $Sigma$ is topologically a plane. Let $X=u_k nu$ where $norm(nd u_k)_(L^2)->0$ and 
$u_k->1$ pointwise. For $k$ sufficiently large $I(X,X)$ will be negative.

#h(-2em)
#strong[Exercise:] Such sequence of $u_k$ exists on $RR^2$.
]

#slide[
#theorem(numbering:none)[
  For $n<=5$, a complete 2-sided stable minimal surface $Sigma^n->RR^(n+1)$ is a flat $RR^n$.
]
This was proved in a series of papers by Fischer, Colbrie, Schoen, do Carmo, Peng, Pogorelov, Chodosh, Li,
Minter, Stryker, and Mazet.

- $n=6$ is still open.
- $n=7$. There exists the (area-minimizing) Simons cone $
    C_(4,4)={(x,y) in RR^4 times RR^4:abs(x)^2=abs(y)^2} 
  . $ And there exists a complete area minimizing hypersurface asymptotic to it.
- $n>=8$. There exist area minimizing graphs which also comes from the Simons cone.

#pagebreak()

We could say more about minimal graphs:
#theorem(numbering:none)[
  Let $Omega cc RR^n$ open, a minimal graph $Gamma(u)$ where $u:Omega->RR$ is stable.
]
Combine this with the last theorem we have 
#corollary(numbering:none)[
  $n<=5$, there are no entire minimal graphs in $RR^(n+1)$ other than flat hyperplanes.
]
#v(2cm)
#line(length:100%)
Next, let's consider when ambient manifold $M$ is a closed manifold.
]

== Stable varifolds
#slide[
#example(numbering:none)[
  $SS^n cc SS^(n+1)$ under round metric is unstable.
] #h(-2em)
One can directly verify by letting $X=nu$ in 2nd variation formula. The same will hold for any closed 2-sided
minimal hypersurface in $M$ with positive Ricci curvature.

#example(numbering:none)[
  $SS^k times {0} cc SS^k times SS^ell$ under the standard metric is stable.
] #h(-2em)
To show this, firstly the $SS^k$ factor is actually totally geodesic $=>II=0$. Then note that under the product
metric any cross term in curvature are also 0. So there are no negative terms in the variation formula.

On negatively curved manifolds we should expected there exist a lot of stable submanifolds as the curvature 
term is positive.

#pagebreak()

If we loose the regularity condition on $Sigma$, things will become more complicated. As there will be no
globally defined unit normal in general, and the divergence theorem may not be applicable.

We shall consider in a more general class of "submanifolds": _integral varifolds_. An $n$-dimensional integral
varifold $M$ has the following properties:
- Up to an $cal(H)^n$ null set, $M$ is the union of countably many $C^1$-images of $RR^n$. And $M$ has locally
  finite $cal(H)^n$ measure, #ie locally finite area.
- For a.e. $p in M$, we could define a tangent space $T_p M$. And then there are proper notion of minimality 
  and stability.
- $M$ could have multiplicity, which takes integer value a.e..

One should take piecewise smooth submanifolds as model of integral varifolds.
]
#slide[
#example(numbering:none)[
  A rectangle in $RR^2$ is #text(red)[not] minimal. Although the classical
  mean curvature on each side is 0. But it should be considered to have a inner pointing $delta$-function mean 
  curvature vector at corners.
]
#example(numbering:none)[
  Two perpendicular lines in $RR^2$ is a minimal varifold. And it is also stable. It seems one can break 
  the crossing to make the length smaller but it is actually impossible with $C^1$ variations.
]
#figure(image("figures/varifolds.svg", width: 70%))
]

#slide[
Particularly, 1-dimensional minimal varifolds could be formulated as geodesic nets. To be precise,
#definition(numbering:none)[
A _geodesic net_ on a Riemannian manifold $M$ is defined to be a set of geodesics with a set of nodes.
Each end of a geodesic is either going to infinity or connecting to a node. And at each node, the direction
vector of geodesics starting from it sum to 0.
]
#theorem(numbering:none,name:"Lawson-Simons 1973")[\
  There are no stable varifolds on round $SS^n$
]
The idea of proof is to find "universal decreasing" vector fields that decrease volume for any varifold.
Let's start with the simplest case when $Sigma$ is 1-dimensional.
]

#slide[
#proposition(numbering:none)[
  For a geodesic net ${gamma_i}_(i in I)$ on $(M,g)$ and variation field $X$, the 2nd variation is given by $
    I(X,X)=sum_i int_(gamma_i) |\(nd_(gamma'_i) X\)^perp|^2-R(X,gamma'_i,gamma'_i,X)dd(s)
  . $ When $M$ is 2-dimensional, let $K$ be its Gaussian curvature, then $
    I(X,X)=sum_i int_(gamma_i) (u'_i)^2-K u_i^2dd(s)
  , $ where $u_i$ is the normal part of $X$ along $gamma_i$.
]
From the proposition, we see a decreasing vector field should not change a lot on normal direction. On $SS^2$,
let $X$ be the projection of $pt_z$ in $RR^3$ to the unit sphere. One can check that on any geodesic (an arc
on some great circle), $u'_i$ is identically 0.
]

#slide[
The same arguments can be generalized to rotation symmetric bodies. Let $M$ be a topological sphere with
metric $
  g=dd(r)^2+f(r)^2 dd(theta)^2
. $ Then $X=f(r)pt_r$ is universal decreasing as long as $K>0$.
#remark(numbering:none)[
  This can be generalized to $M^n$ with metric $
    g=dd(r)^2+f(r)^2 g_theta
  $ where $g_theta$ is a metric on $SS^(n-1)$ independent of $r$. In particular, there are no stable geodesic
  nets on $SS^n$.
]

For $k>1$ dimensional varifolds on $SS^n$, $pt_(x^j)|_(T SS^n)$ is no longer universal decreasing. But we can 
still prove that $I$ has a negative eigenvalue.

#pagebreak()
Let's assume $Sigma^k->SS^n into RR^(n+1)$ is piecewise smooth. General case could be proved by more careful 
computations of the 2nd variation.

#proof(name:"(smooth case of L-S)")[\
Let $v_j=pt_(x^j)|_(T SS^n)$, choose orthonormal basis ${e_i}$ such that $T Sigma^k=span{e_1,...,e_k}$,
and let $nu$ be the unit normal of $SS^n$ in $RR^(n+1)$, then #v(-16pt) $
  I(v_j,v_j)=k(k-1)pari(v_j,nu)^2-k sum_(i=1)^n pari(v_j,e_i)^2+sum_(i=1)^k pari(v_j,e_i)^2
. $ #v(-16pt) Let $V=span{v_1,...,v_(n+1)}$, we have $
  tr_V I(dot.c,dot.c)=-k(n-k)<0
. $ Hence $I$ cannot be positive semi-definite and $Sigma$ is unstable.
]
]

#slide[
#strong[Conjecture.] On strictly quarter-pinched $n$-spheres there are no stable varifolds of dimension $0<k<n$.

#example(numbering:none)[
  $CC PP^n$ under Fubini-Study metric has $1/4<=K_sigma<=1$ and non-trivial $H_2$. So the strictly pinch 
  condition cannot be removed for $n>=4$.
]
#example(numbering:none)[
  Let $Sigma^2 into RR^3$ be a smoothed thin triangular prism, which is convex and thus has positive $K$.
  But there exists a stable geodesic net as shown in the picture:
  #v(-20pt)
  #figure(image("figures/thin_triangle.png", width:55%))
]

#pagebreak()

To eliminate such examples, consider a geodesic that goes back to start. Let $X=sin((pi t)/ell) nu$ along
it where $t$ is the arclength parameter and $ell$ is the total length. $K<=1$ implies $ell>=2pi$, then $
  I(X,X)=1/(2l)(pi^2-K ell^2)<=1/(2ell)(pi^2-1/4 dot.c (2pi)^2)=0
, $ provided by $K>=1/4$. The equality cannot hold, so this cannot happen on quarter-pinched spheres.

#pagebreak()

#example(numbering:none)[
  Choose coordinate on $SS^3 into RR^4 iso CC^2$ by $
    {(e^(i theta)cos r,e^(i vphi)sin r):r in [0,pi\/2],theta,vphi in [0,2pi]}
  . $ Define the Berger's metric with parameter $lambda>-1$ by $
    g=dd(r)^2+cos^2 r dd(theta)^2+sin^2 r dd(vphi)^2+lambda (cos^2 r dd(theta)+sin^2 r dd(vphi))^2
  . $ Using the same vector fields as for the round sphere shows that if $-1/2<lambda<2$, then there will
  be no stable geodesic nets. The critical case $lambda=-1/2$ is $1\/5$-pinched. When $lambda=-1/2$, the Hopf 
  fiber $
    {(e^(i t)cos r_0,e^(i t)sin r_0):t in [0,2pi]}
  $ is stable, so the bound is sharp.
]
]

#slide[
Following the idea from Lawson-Simons, we know 
#theorem(name:"Franz-Trinca 2023",numbering:none)[
  
]
]
