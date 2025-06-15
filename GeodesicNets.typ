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
    title: [Stability of geodesic nets],
    author: text(font: "LXGW WenKai", weight:400)[薛皓天],
    date: datetime.today(),
    institution: [Stanford University],
  ),
)

#title-slide()

== Minimality and stability
#slide[
Let $(M^(n+k),g)$ be a Riemannian manifold, $F:Sigma^n->M$ be an smooth immersed submanifold with smooth
boundary. The area of $Sigma$ is calculated by $
  cal(A)(Sigma)=int_Sigma 1 dd(mu_g)=int_Sigma sqrt(det \(g_(alpha beta)pt_i F^alpha pt_j F^beta\)) dd(x)
. $ 
Consider a smooth family $F_t:Sigma times (-eps,eps)->M$ with $F_0=F$ and $F_t$ only differ from $F$
on a compact set in $Sigma\\pt Sigma$.

Let $X=lr(dv(,t)|)_(t=0)$ be the variation field. The 1st variation is given by $
    lr(dv(,t)|,size:#48pt)_(t=0)cal(A)(Sigma_t)=int_Sigma div_Sigma X dd(mu_Sigma)
    =int_(pt Sigma)X dot.c nu_(pt Sigma) dd(mu_(pt Sigma))-int_Sigma X dot.c H dd(mu_Sigma)
, $ where $H$ is the mean curvature of $Sigma$.

$Sigma$ is said to be _minimal_ or _stationary_ if the 1st variation is 0 for any compactly supported $X$,
which is true if and only if $H=0$.

If we want to know whether $Sigma$ actually minimizes area (at least locally), we need to calculate the 2nd 
variation. Suppose $Sigma$ is minimal, #ie $H=0$, and suppose $X perp T Sigma$, then $
  I(X,X):=&lr(dv(#[]^2,t^2)|,size:#48pt)_(t=0)op("Area")(Sigma_t) \
  =&int_Sigma |\(hat(nd) X\)^perp|^2-|X dot.c II(dot.c,dot.c)|^2-sum_(i=1)^n R(X,e_i,e_i,X)
. $ $Sigma$ is said to be _stable_ if $I(X,X)>=0$ for any compactly supported smooth normal field $X$.
]

#slide[
#example(numbering:none)[
  Helicoid, Catenoid in $RR^3$ are unstable.
  #figure(
    grid(
      columns: 2,
      gutter: 2mm,
      image("figures/helicoid.svg", width: 100%),
      image("figures/catenoid.svg", width: 100%),
    ),
  )
]
#theorem(name: "A lot of people",numbering:none)[\
  For $n<=5$, a complete 2-sided stable minimal surface $Sigma^n->RR^(n+1)$ is a flat $RR^n$.
]
#pagebreak()

- $n=2$ was proved by Fischer-Colbrie–Schoen, do Carmo–Peng and Pogorelov;
- $n=3$ was proved by Chodosh-Li;
- $n=4$ was proved by Chodosh-Li-Minter-Stryker;
- $n=5$ was proved by Mazet.
- $n=6$ is still open.
- $n=7$ there exists Simons cone, which is area minimizing.
- $n>=8$ is false. There exist area minimizing graphs.

#example(numbering:none)[
  $SS^n cc SS^(n+1)$ under round metric is unstable.
] #h(-2em)
One can directly see this by letting $X=nu$ in 2nd variation formula. The same holds for any closed 2-sided
minimal hypersurface in $M$ with positive Ricci curvature.

#example(numbering:none)[
  $\(SS^1\)^(times k) cc bb(T)^n$ under flat metric is stable.
] #h(-2em)
The negative terms in 2nd variation are 0 in this case.
]

== Stable varifolds
#slide[
If we loose the regularity condition on $Sigma$, things will become more complicated. There will be no globally
defined unit normal in general and the divergence theorem may not be applicable.
#definition(numbering:none)[
  A _integral varifold_ is a pair $(M,theta)$ where $M$ is a countably $n$-rectifiable set and $theta$ is 
  an positive integer valued $cal(H)^n$-measurable function on $M$, called the _multiplicity function_.
  Moreover, we require $M$ to have locally finite $cal(H)^n$-measure to prevent ill behaved examples.
] #h(-2em)
Roughly speaking, varifolds are submanifolds allowing singular components and multiplicities. 

One important property of varifolds is they have a.e. defined  tangent spaces and thus well-defined notion 
of minimality and stability
]
#slide[
#example(numbering:none)[
  A rectangle in $RR^2$ is a varifold with $theta==1$. It is #text(red)[not] minimal. Although the classical
  mean curvature on each side is 0. But it should be considered to have a inner pointing $delta$-function mean 
  curvature vector at corners.
]
#example(numbering:none)[
  Two perpendicular lines in $RR^2$ is a minimal varifold. And it is also stable. It seems one can break 
  the crossing to make the length smaller but it is actually impossible using $C^1$ variations.
]
#figure(image("figures/varifolds.svg", width: 70%))
]

#slide[
The most simplest examples of minimal varifolds are geodesic nets. To be precise,
#definition(numbering:none)[
A _geodesic net_ on a Riemannian manifold $M$ is defined to be a set of geodesics with a set of nodes.
Each end of a geodesic is either going to infinity or connecting to a node. And at each node, the direction
vector of geodesics starting from it sum to 0.
]
#theorem(numbering:none,name:"Lawson-Simons 1973")[\
  There are no stable varifolds on round $SS^n$
]
The idea of proof is to find "universally decreasing" vector fields that decrease volume for any varifold.
Let's illustrate their proof for $SS^2$.
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
let $X$ be the projection of $pt_z$ in $RR^3$ to the unit sphere. One can check that for any geodesic (an arc
on some great circle), $u'_i$ is identically 0.
]
