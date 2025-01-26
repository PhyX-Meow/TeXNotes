#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  numbering: "1.1.",
)

#align(center)[#text(20pt)[
  *Local Regularity of Weak Solutions*
]#v(0.5cm)]

Consider the general form elliptic equation $
  cal(L)u=sum_(abs(alpha),abs(beta)<=m) nd_beta (a^(alpha beta)nd_alpha u)=
  sum_(abs(alpha)<=m)nd_beta f^beta.
$ Where $
  nd_alpha=nd^m_(alpha_1,...,alpha_n)
  =pdv(#[]^(alpha_1),x_1^alpha_1)dots.c pdv(#[]^(alpha_n),x_n^alpha_n)
$ 
A weak solution $u$ in $H^m$ is such that for any $v in H_0^m ("or" C_0^oo)$, $
  B(u,v)=sum_(abs(alpha),abs(beta)<=m) int_Omega a^(alpha beta) nd_alpha u nd_beta v=
  sum_(abs(beta)<=m)int_Omega f^beta nd_beta v
$ To prove local regularity, we do energy estimate. The conditions we assume are
+ $a^(alpha beta) in L^oo$ on ambient ball $B(0,1+eps)$, and is uniformly elliptic in
  highest symbol, #ie $
    sum_(abs(alpha),abs(beta)=m)a^(alpha beta)xi_alpha xi_beta
    >=Lambda abs(xi)^2 quad "for some" Lambda>0
  $ 
+ $f^(alpha) in L^2$ on $B(0,1+eps)$.
From now on, we denote $B(0,1)$ by $B$ and $B(0,theta),theta<1$ by $B'$, and we use
$norm(dot.c)$ and $norm(dot.c)'$ for norm on $B$ and $B'$ respectively.

#lemma[
  If $u$ is a $H^m$ weak solution, we have inner energy estimate $
    norm(u)'_(H^m)<=C lr((norm(u)_(L^2)+sum_(abs(beta)<=m)
    norm(f^beta)_(L^2)), size:#50%)
  $ 
]
#proof[
  Let $eta$ be our favorite cut-off function that is 1 on $B'$ and supported on $B$,
  let $v=eta^(2m) u in H_0^m$. Then we have $
    sum_(abs(alpha),abs(beta)=m)int_B a^(alpha beta)eta^(2m) nd_alpha u nd_beta u
    &=sum_(abs(alpha),abs(beta)=m)int_B a^(alpha beta)nd_alpha u
    (eta^(2m) nd_beta u-nd_beta (eta^(2m) u)) \ 
    &-sum_(abs(alpha)<m,abs(beta)<=m)+sum_(abs(alpha)=m,abs(beta)<m)
    int_B a^(alpha beta) nd_alpha u nd_beta (eta^(2m) u) \
    &+sum_(abs(beta)<=m)int_B f^(beta) nd_beta (eta^(2m) u).
  $ We have that $
    "LHS">=Lambda int_B eta^(2m)sum_(abs(alpha)=m)abs(nd_alpha u)^2
  $ and $
    "RHS"<=C(eta,cal(L))int_B eta^m sum_(abs(alpha)<=m) abs(nd_alpha u)
    lr((sum_(abs(beta)<m) abs(nd_beta u)+sum_(abs(beta)<=m) abs(f^(beta))), size:#50%)
  $ Use the fact that $
    a b<=eps a^2+C(eps)b^2
  $ We get $
    lambda norm(u)'^2_(H^m)<=^"Poincaré ineq."
    Lambda/2 int_B eta^(2m)sum_(abs(alpha)=m)abs(nd_alpha u)^2
    <=C(eta,cal(L))lr((norm(u)_(H^(m-1))^2+sum_(abs(beta)<=m)norm(f^(beta))_(L^2)^2),
    size:#50%)
  $
]
