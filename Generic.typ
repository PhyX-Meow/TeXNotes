#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "cambria",
  numbering: "1.1.",
)
#show heading: it => {counter(math.equation).update(0); it} 

#align(center)[#text(20pt)[
  *Generic Singularities*
]#v(0.5cm)]

= Intro
- MCF always extinct $=>$ Singularities cannot be avoided.
- #emph[Huisken's monotonicity formula] implies asymptotically self-similar near a
  given singularity.

#definition[
  A one-parameter family $M_t$ (in local coordinates) of hypersurfaces in $RR^(n+1)$
  is a MCF if $
    dot(x)^perp=(pt_t x)^perp=H
  . $ Where $
    H=-abs(H)bold(n),quad abs(H)=div bold(n)
  . $ 
]

The $n$-sphere of radius $R$ has mean curvature $n/R$, pointing to where it "curves".
And the cylinder $SS^k times RR^(n-k)$ of radius $R$ has $abs(H)=k/R$.

#example[
  The shrinking spheres $
    M_t=sqrt(-2n t)SS^n cc RR^(n+1),quad t in (-oo,0)
  $ is a (self-similar) MCF.
]

#theorem[
  Any smooth compact convex initial hypersurface remains smooth and convex
  under MCF. And any smooth curve in $RR^2$ will eventually become convex and then
  extinct under 2 dim MCF i.e. CSF.
]

#definition[
  A #emph[self-shrinker] is a MCF $M_t$ satisfying $
    M_t=sqrt(-t)M_(-1)
  . $ For example: the shrinking sphere.
]

#definition[
  The #emph[tangent flow] of a MCF $M_t$ at $(x_0,t_0)$ is defined as follows: First
  translate $(x_0,t_0)$ to $(0,0)$. Then let $lambda_j->oo$ be a sequence of dilation
  factors. Let $(x,t)|->(lambda_j x,lambda_j^2 t)$ we get MCF's $
    M_t^(j)=lambda_j M_(lambda_j^(-2)t)
  . $ Using #emph[Huisken's monotonicity formula] and #emph[Brakke's compactness
  theorem] we can prove there is a subsequence converges weakly to a limit flow
  $cal(T)_t$. Moreover, $cal(T)_t$ is a self-shrinker. (Note that it is not known
  whether $cal(T)_t$ is unique).
]

#definition[
  A hypersurface is called #emph[mean convex] if $H>=0$.
]

#definition(name: "Gaussian surface area and entropy")[
  Let the $F$-functional for a hypersurface $Sigma$ defined by: $
    F_(x_0,t_0)(Sigma)=(4pi t_0)^(-n/2)int_Sigma e^((-abs(x-x_0)^2)/(4t_0))dd(mu)
  . $ The #emph[entropy] of $Sigma$ is defined as $
    lambda(Sigma)=sup_(x_0 in RR^(n+1),t_0>0) F_(x_0,t_0)(Sigma)
  . $ 
]

- The critical point of $F_(x_0,t_0)$ are exactly those $Sigma$ that is a
  self-shrinking solution at $t=-t_0$ and extinct at $x=x_0$.
- $lambda$ is non-negative and invariant under dilations, rotations and translations.
- $lambda$ is non-increasing under MCF.
- The critical points of $lambda$ are self-shrinkers of MCF.

But the entropy may not depend on $Sigma$ smoothly. To resolve this, we define
a self-shrinker to be #emph[entropy-stable] if it is a local minimum of $lambda$.
Here "local" means among hypersurfaces that can be written as a graph of $Sigma$
of a function that small in $C^2$.


= F-functional and Huisken's monotonicity formula
Define $
  Phi(x,t)=(-4pi t)^(-n/2)e^(abs(x)^2/(4t))
. $ Note that $Phi$ is non-negative on $RR^(n+1)times (-oo,0)$. Then set
$Phi_(x_0,t_0)(x,t)=Phi(x-x_0,t-t_0)$. If $M_t$ is a MCF, and $u$ is $C^2$, then $
  dv(,t)int_(M_t)u Phi_(x_0,t_0)=-int_(M_t)
  lr(abs(H-((x-x_0)^perp)/(2(t-t_0))), size:#80%)^2
  u Phi_(x_0,t_0)+int_(M_t)(dot(u)-lap u)Phi_(x_0,t_0)
. $ 

#proof[
  Wlog assume $x_0=0,t_0=0$,
  First we consider the case $u==1$,
  $
    dv(,t)int_(M_t)Phi dd(sigma_t)
    =int_(M_t)dot(Phi)+nd_H Phi-abs(H)^2 Phi dd(sigma_t)
    =int_(M_t)(-abs(H)^2-n/(2t)-abs(x)^2/(4t^2)+(x dot.c H)/(2t))Phi dd(sigma_t)
  . $ Let $Y=x/(2t)Phi$ be a vector field, we have $
    int_(M_t)(x dot.c H)/(2t)Phi dd(sigma_t)&=int_(M_t)H dot.c Y dd(sigma_t)
    =-int_(M_t)div_g Y dd(sigma_t) \
    &=int_(M_t)-1/(2t)lr((Phi div x+x dot.c nd Phi-bold(n)dot.c nd_(bold(n))(x Phi)),
    size:#150%) dd(sigma_t) \
    &=int_(M_t)-1/(2t)((n+1)+abs(x)^2/(2t)-1-abs(x^perp)^2/(2t)) Phi dd(sigma_t) \
    &=int_(M_t)(-n/(2t)-abs(x)^2/(4t^2)+abs(x^perp)^2/(4t^2))Phi dd(sigma_t)
  . $ Hence $
    dv(,t)int_(M_t)Phi dd(sigma_t)
    =int_(M_t)(-abs(H)^2+(x dot.c H)/t-abs(x^perp)^2/(4t^2))Phi dd(sigma_t)
    =-int_(M_t)abs(H-x^perp/(2t))^2 dd(sigma_t)
  . $ For general $u$, we consider $Y=x/(2t)u Phi$, this time we get  $
    int_(M_t)(x dot.c H)/(2t) u Phi
    =int_(M_t)(-n/(2t)-abs(x)^2/(4t^2)+abs(x^perp)^2/(4t^2)) u Phi
    -1/(2t)lr((x dot.c nd u-bold(n)dot.c x nd_(bold(n))u),size:#150%)Phi
  . $ Then $
    &#hide[=]dv(,t)int_(M_t)u Phi dd(sigma_t)-int_(M_t)(dot(u)-lap u)Phi dd(sigma_t) \
    &=int_(M_t)u dot(Phi)+(lap u)Phi+nd_H (u Phi)-abs(H)^2 u Phi dd(sigma_t) \
    &=int_(M_t)(-abs(H)^2-n/(2t)-abs(x)^2/(4t^2)+(x dot.c H)/(2t))u Phi
    +(lap u)Phi+(nd_H u)Phi dd(sigma_t) \
    &=int_(M_t)-abs(H-x^perp/(2t))^2+(1/(2t)x dot.c nd u-(bold(n)dot.c x)/(2t)
    nd_bold(n)u)Phi+(lap u)Phi+(nd_H u) Phi dd(sigma_t) \
    &=int_(M_t)-abs(H-x^perp/(2t))^2+(1/(2t)x dot.c nd u-(bold(n)dot.c x)/(2t)
    nd_bold(n)u)Phi+(lap u)Phi-div_g ((nd u)Phi) dd(sigma_t) \
    &=int_(M_t)-abs(H-x^perp/(2t))^2 dd(sigma_t)
  . $ 
]

Something here...

= Self-shrinkers and self-shrinkering MCF

An initial self-shrinker is defined to satisfy
#math.equation(
  block: true,
  numbering: num => "(" + (counter(heading).get() + (num,)).map(str).join(".") + ")",
  supplement: none,
  $ H=-(x dot.c bold(n))/2,quad #ie quad x dot.c H=-2abs(H)^2
. $) <initial-shrinker>
#lemma[
  If a hypersurface $Sigma$ satisfies @initial-shrinker, then $M_t=sqrt(-t)Sigma$
  is a MCF satisfying $
    H_(M_t)=-(x dot.c bold(n)_(M_t))/(2t)
  . $ Conversely if a MCF satisfy $M_t=sqrt(-t)M_(-1)$, then the above equation
  is satisfied
]

#corollary[
  If $M_t$ flow by mean curvature, then $M_t$ is a self-shrinker (to 0) if and only if
  $int_(M_t)Phi$ is constant.
]
#corollary[
  If $Sigma$ is a self-shrinker and $H==0$, then it is a minimal cone. In particular
  if $Sigma$ is smooth embedded, it is a hyperplane through the origin.
]
