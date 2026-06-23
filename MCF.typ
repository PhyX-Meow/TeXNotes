#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  heading-font: "miama",
  numbering: "1.1.",
)

#title(font:"miama")[
  Notes on MCF (Multiplicity One)
]

#let kpa = math.kappa
#let indent = h(0em) + v(0em, weak:true)
#show math.equation: set math.lr(size:0pt)
#show math.chevron.l: set text(size:14pt)
#show math.chevron.r: set text(size:14pt)
#let lr(body,s:100%+0pt) = math.lr($(body)$, size:s)
#let bigl(body,s:100%+0pt) = math.lr(body, size:s)

= Preliminaries on MCF
== Definitions
We always live in the spacetime $RR^(n+1)_(x)times RR_t$. The neighborhood in spacetime are the _parabolic
balls_ $
  P(x,t,r):=B(x,r)times [t-r^2,t+r^2],quad P_-(x,t,r):=B(x,r)times [t-r^2,t]
. $ Note that the range of $t$ are closed intervals. Also the _parabolic rescaling_ is defined by $
  lambda (cal(M)-(x_0,t_0)):={(lambda(x-x_0),lambda^2(t-t_0)):(x,t)in cal(M)}
. $ $cal(M)cc RR^(n+1)times I$ is called _regular_ at $(x,t)$ if it is a smooth hypersurface around $(x,t)$
with locally non-vanishing $dd(t)$, #ie projection of $pt_t$ onto $cal(M)$ is non-zero. For $u$ defined on
$cal(M)$, let the _normal time derivative_ $dot(u):=pt_tau u$ where $dd(t)(pt_tau-pt_t)=0$. We might abuse
$pt_t$ to refer to $pt_tau$ for calculations on $cal(M)_"reg"$. 

$cal(M)$ is called a smooth _mean curvature flow_ if $
  dot(x)=H
, $ or equivalently $pt_tau=pt_t+H$. $cal(M)$ is called a _weak set flow_ if it is a closed subset that 
avoids any compact smooth MCF. It is called maximal or _level set flow_ if it cannot be extended.
- A smooth MCF with compact time slabs over compact time intervals is a level set flow.
- A level set flow without singularities is a smooth MCF.

For any closed, smooth, embedded hypersurface $Sigma cc RR^(n+1)$ there is a unique level set flow $cal(M)
cc RR^(n+1)times [0,oo)$ with $cal(M)_0=Sigma$. However, such $cal(M)$ may _fatten_ #ie has non-empty interior.

Let $K_+$ be the compact region bounded by $Sigma$ and $K_-=ov(K_+^c)$, and $cal(K)_plus.minus$ be the unique 
level set flow from $K_plus.minus$. Then $cal(M)_+,cal(M)_-:=pt cal(K)_plus.minus$ is called the _outermost_
and _innermost_ flow from $Sigma$.

On the other hand, the _Brakke flow_ is a family of Radon measures $(mu_t)_(t in I)$ such that 
+ For a.e. $t$ $mu_t$ is $n$-rectifiable with locally $L^1$ mean curvature.
+ $int_(t_1)^(t_2)int_K abs(H)^2 dd(mu_t)dd(t)<oo$ for any $K$ compact and $[t_1,t_2]cc I$.
+ For any $[t_1,t_2]cc I$ and non-negative $u in C_0^1 (RR^(n+1)times [t_1,t_2])$, #h(1fr) $
    bigl(int_(R^(n+1))u dd(mu_t)|)_(t=t_1)^(t_2)
    <=int_(t_1)^(t_2)int_(RR^(n+1))(pt_t+H)u-u abs(H)^2 dd(mu_t)dd(t)
  . $ Note that for a smooth MCF, the inequality takes equality.

The support of $(mu_t)$ is defined to be  $
  cal(M):=ov(union.big_(t in I)(op("supp")mu_t)times {t})
. $ This closure is a weak set flow.

For $t<t_0$, let $
  rho(x_0,t_0)(x,t)=1/(4pi(t_0-t))e^((-|x-x_0|^2)/(4\(t_0-t\)))
. $ We have $
  Theta_(x_0,t_0)(t):=int_(RR^(n+1))rho_(x_0,t_0)(dot.c,t)dd(mu_t)
  $ is non-increasing in $t$. Then we can define the Gaussian density $
  Theta_(x_0,t_0)=lim_(t->t_0)Theta_(x_0,t_0)(t)
. $ Note that $Theta_(x_0,t_0)>=1$ if and only if $(x_0,t_0)$ is contained in the support of $(mu_t)$.
And $(mu_t)$ is called _unit-regular_ if it is regular near points with $Theta_(x_0,t_0)=1$. Also define $
  Theta(mu_t)=sup_((x_0,t_0)\ t<t_0)Theta_(x_0,t_0)(t)
. $
#remark[
  This is a quantity like volume growth rate for minimal surfaces.
]

== Local scale and almost regular
