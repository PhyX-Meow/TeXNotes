#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "",
  numbering: "1.1.",
)

#align(center)[#text(20pt, font:"Miama Nueva")[
  *Notes of Micallef-Moore*
]#v(0.5cm)]

#show heading: it => text(font:"Miama Nueva", it)

= Intro
Let $(M,g)$ be a $n$-dimensional Riemannian manifold, $p in M$. Recall that the curvature can be viewed as 
an operator $
  cal(R):wed^2 T_p M-->wed^2 T_p M,quad
  pari(cal(R)(v wed w),eta wed xi)=pari(R(v,w)xi,eta)
. $ The metric can be extend to a Hermitian metric on $T_p M tens CC$ by $
  pari(v,w)=g(v,bar(w)), quad v,w in T_p M tens CC
. $ The curvature operator is extended $CC$-linearly, we get $
  cal(R):wed^2 T_p M tens CC-->wed^2 T_p M tens CC
. $ To each complex two-plane $Sigma=span{v,w}cc T_p M tens CC$, we can assign a complex sectional curvature
to it $
  K_Sigma=pari(cal(R)(v wed w),v wed w)/abs(v wed w)^2
. $ $v in T_p tens CC$ is called _isotropic_ if $g(v,v)=0$, a complex subspace $V$ is called _totally isotropic_
if every $v in V$ is isotropic. $(M,g)$ is called have positive isotropic curvature or _PIC_ if $K_Sigma>0$
for every totally isotropic 2-plane $Sigma$. Note that the dimension of a totally isotropic subspace is at
most $n/2$. The condition is non-vacuous only for $n>=4$.

For an isotropic vector $xi=v+i w$, we have $
  0=g(xi,xi)=abs(v)^2-abs(w)^2-2v dot.c w
. $ Hence $abs(v)=abs(w)$ and $v perp w$. Thus for an totally isotropic 2-plane $Sigma$, there is a basis 
${v,w}$ such that there is $e_1,...,e_4$ orthonormal with $
  v=e_1+i e_2,quad w=e_3+i e_4
. $ Then $
  v wed w=(e_1wed e_3-e_2wed e_4)+i(e_1 wed e_4+e_2 wed e_3)
, $ and $
  K_Sigma=pari(cal(R)(v wed w),v wed w)=R_(1331)+R_(2442)+R_(1441)+R_(2332)-2R_(1234)
. $ 
