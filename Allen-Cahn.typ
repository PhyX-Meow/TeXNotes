#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "ncm",
  heading-font: "miama",
  numbering: "1.1.",
)

#title(font:"miama")[
  Allen-Cahn Equations
]

#let Ind = math.op("Ind")
#show math.equation: set math.lr(size:12pt)
#show math.chevron.l: set text(size:14pt)
#show math.chevron.r: set text(size:14pt)
#let lr(body,s:100%+0pt) = math.lr($(body)$, size:s)
#let bigl(body) = math.lr(body, size:100%+0pt)

= Introduction
#definition[
  The Allen-Cahn energy is defined by $
    E_eps (u)=int_Omega eps/2 abs(nd u)^2+1/eps W(u)dd(mu_g)
  , $ where $W(t)=1/4 (1-t^2)^2$ is a "double well potential".
]
- The energy is defined for any $u in H^1 sect L^4$. Could be defined to be $oo$ otherwise.

The critical points of Allen-Cahn energy satisfy $
  eps lap_g u=1/eps W'(u)=1/eps u (u^2-1)
. $ 
- A critical $u:M->RR$ is smooth. (Nash-Moser with special argument on $u^3$ term)
- A critical $u$ on closed $M$ has range $[-1,1]$. (maximum principle)
- Trivial solution $u=0,plus.minus 1$.

One dimensional case: $eps u''=1/eps W'(u)$. Rescale we may assume $eps=1$.
- First integral: $p^2=1/2(1-u^2)^2+C$
- $C=0 => u=plus.minus tanh (t-t_0)/sqrt(2)$, with finite energy.
- $C!=0 =>$ infinite energy.
Rescale back we see $u_eps->sgn$ a.e.. Note that ${0}=pt{u_0=1}$.
- Key observation: Boundary of level set of the limit solution is a minimal hypersurface.
- #text(blue)[Solutions on $SS^1$?]

$RR^2$ case:
Let $HH_eps (t)=tanh t/(eps sqrt(2))$. Similarly rescale, we have solutions$
  u(x)=HH(x dot.c v-a)
. $ The level sets of limit are ${x dot.c v=a}$.
- There exists a (entire) saddle solution with ${u_0=0}={x y=0}$.
- There exists solution with ${u=0}$ is asymptotic to $ell_1 union ell_2$ for any two lines.

= Convergence of local minimizers
Recall:
- Compact embedding of functions of bounded variation.
- Sets with finite perimeter.
- Regularity of minimal surfaces:
#theorem[
  If $E cc (M^n,g)$ is a local minimizer of perimeter, $3<=n<=7$. Then after changing $E$ by a null 
  set, $pt E$ is a smooth stable minimal hypersurface.
]

#h(-2em)
$Gamma$-convergence: Let $
  Phi(t):=int_0^t sqrt(2W(s))dd(s)=1/2lr(t-t^3/3,s:#20pt)sgn(1-t^2)
. $ Then $
  E_eps (u)&=int_Omega eps/2 abs(nd u)^2+1/eps W(u)dd(mu_g) \
  &>=int_Omega sqrt(2W(u))abs(nd u)dd(mu_g)=int_Omega abs(nd (Phi(u)))dd(mu_g)
. $ 
#theorem[
  Let $Omega cc (M,g)$ precompat open, ${u_eps}$ #st $E_eps (u_eps)<=C$. Then there is subsequence 
  converges to $u_0$ weakly in $op("BV")_"loc" (Omega)$, strongly in $L^1_"loc"$ with $u_0 in {pm 1}$
  a.e.. Moreover $
    sigma cal(P)_Omega' ({u_0=1})<=liminf_(eps->0) E'_eps (u_eps)
  , $ where $sigma=Phi(1)-Phi(-1)$, $Omega'cc cc Omega$.
] Actually any set with finite perimeter can be recovered this way.
#theorem[
  For any $E cc Omega$ with finite perimeter, there is a sequence $u_eps in H^1 sect L^4$ with $
    sigma cal(P)_Omega=lim_(eps->0)E_eps (u_eps)
  , $ and $u_eps->Id_E-Id_(Omega\\E)$ in $L^1$.
]

#h(-2em)
Convergence of local minimizers: Let $(M,g)$ be closed Riemannian manifold.
#definition[
  $u in H^1 sect L^4$ is called a _(strict) ($delta$-)local minimizer_ of $E_eps$ if there is
  $delta>0$ #st $E_eps (v)(>)>=E_eps (u)$ for any $v$ $delta$-close to $u$ in $L^1$.

  Similarly $E cc Omega$ is _(strict) local minimizer_ of perimeter if there is $delta>0$ #st 
  $cal(P)_Omega (F)(>)>=cal(P)_Omega (E)$ for any $F$ with $Id_F$ $delta$-close to $Id_E$ in $L^1$.
]
#theorem[
  Let ${u_eps}$ be $delta$-local minimizers of $E_eps$ with $E_eps (u_eps)<=C$. Then there is 
  subsequence converges to $u_0 in op("BV")$, $u_0 in {pm 1}$ a.e., and ${u_0=1}$ is a local 
  minimizer of perimeter.
]
#theorem[
  For any $E cc (M,g)$ strict local minimizer of perimeter. There exist ${u_eps}$ locally minimizing
  $E_eps$ such that $u_eps->Id_E-Id_(M\\E)$ in $L^1$ and $lim_(eps->0)E_eps (u_eps)=sigma cal(P)(E)$.
]

= Non-minimizing solutions
