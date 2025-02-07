#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  numbering: "1.1.",
)

#show heading.where(level: 1): it => block(width: 100%)[
  #set align(center)
  #set text(size:20pt, font: "Miama Nueva")
  #it.body
  #v(12pt)
]
#show heading.where(level: 2): it => text(font: "Miama Nueva", it) + v(12pt)
= Geometry
== Geodesic flow
#theorem[
  Let $G$ be a locally compact Lie group with at most countably many connect
  components, $X$ a locally compact Hausdorff space. Suppose $G acts X$
  continuously, then for $x in X$ such that $G dot.c x$ is closed, $
    G\/G_x->G dot.c x
  $ is a homeomorphism, where $G dot.c x$ is equipped with the subspace topology.
  If further $M$ is a manifold and the action is smooth, $G dot.c x$ will be
  a embedded submanifold and the map above is smooth. (Note that in this case,
  the quotient $G->G dot.c x$ will be a smooth submersion and $G_x$ is a
  properly embedded Lie subgroup).
]
#proposition[
  Let $M$ be a complete Riemannian manifold and $alpha:RR->M$ be a complete
  geodesic. Suppose $Im alpha$ is compact, then $alpha$ is closed.
]
#proof[
  $alpha$ can be uniquely lift to a path on the sphere bundle $S(T M)$ by $
    tilde(alpha)(s)=(alpha(s),alpha'(s))
  . $ It is actually the integral curve of $
    X_(x,v)=v^k pdv(,x^k)+Gamma_(i j)^k v^i v^j pdv(,v^k)
  $ on $T M$. $X$ generates Lie group action of $RR acts T M\\ M$. We can
  conclude the result by theorem above. Or by the following argument:

  Suppose $alpha$ is not closed, #ie $tilde(alpha)$ is non-periodic. Then there
  is ${s_k}->oo$ such that $tilde(alpha)(s_k)->p$. But $Im tilde(alpha)$ is
  compact (by the compactness of unit sphere), so $p=tilde(alpha)(s_0)$. Hence
  $tilde(alpha)(s_0)$ is a limit point of $Im tilde(alpha)$. Since $RR$ acts
  transitively on $Im tilde(alpha)$, $Im tilde(alpha)$ is a perfect set.
  Choose a small codim 1 submanifold $W$ through $p$ that is transverse to $X$.
  Then $Im tilde(alpha)$ can only hit $W$ countably many times while $W sect
  Im tilde(alpha)$ is a perfect set. Contradiction.
]

== Removable Singularity
#let Eps = math.cal("E")
#proposition[
  Let $F:D\\{0}->M into RR^k$ be a smooth harmonic map with finite energy, then $F$ can be extend to a smooth
  harmonic map $D->M$.
]
#proof[
  First notice that $F$ is a weakly harmonic map on $D$ since $H_0^1 (D\\{0})=H_0^1 (D)$. We only need to prove
  that $F$ is in $W^(1,p)$ for some $p>2$ then we can bootstrap to show $F in C^oo$.

  Change coordinate $(r,theta)arrow.squiggly.r(t,theta)$ where $r=e^(-t)$, the metric becomes $
    dd(r)^2+r^2 dd(theta)^2=e^(-2t)(dd(t)^2+dd(theta)^2) ~ dd(t)^2+dd(theta)^2 quad "conformally"
  . $ Write $
    F_T:[0,oo)times SS^1-->M,quad (t,theta)|-->F(t-T,theta)
  . $ Note that $
    Eps(F_T)=Eps(F|_(r<=e^(-T)))->0 "as" T->oo
  $ So there is a subsequence converges in $C_"loc"^oo$ to a constant (may depend on the subsequence).

  We claim that: $
    int_(t=t_0) abs(F_t)^2dd(theta)=int_(t=t_0)abs(F_theta)^2dd(theta)
  . $ This is true since $
    1/2 dv(,t) int_(t=t_0) abs(F_t)^2-abs(F_theta)^2dd(theta)
    &=int_(t=t_0)F_(t t)dot.c F_t-F_(t theta)dot.c F_theta dd(theta) \
    &=int_(t=t_0)(F_(t t)+F_(theta theta))dot.c F_t-pt_theta (F_t dot.c F_theta) dd(theta) \
    &=0 quad "since" F "is conformal and" lap F perp T M
  . $ Hence LHS $-$ RHS is a constant. Note that $
    abs(int_0^oo #h(-.4em) int_0^(2pi)abs(F_t)^2-abs(F_theta)^2 dd(theta)dd(t))<=
    int_0^oo #h(-.4em) int_0^(2pi)abs(F_t)^2+abs(F_theta)^2 dd(theta)dd(t)=Eps(F)<oo
  , $ the constant has to be 0.

  Now let $
    p(t)=int_0^(2pi) abs(F_theta)dd(theta)
  . $ By the convergence we know $abs(nd F)->0$ as $t->oo$, we have $
    1/2 p''(t)&=int_0^(2pi) abs(F_(t theta))^2+F_theta dot.c F_(t t theta)dd(theta) \
    &=int_0^(2pi) abs(F_(t theta))^2-F_(theta theta) dot.c F_(t t)dd(theta) & "(by parts)" \
    &=int_0^(2pi) abs(F_(t theta))^2+abs(F_(theta theta))^2-A(nd F,nd F)dot.c F_(theta theta)dd(theta)
    & quad quad "(equation)" \
    // text(#red, &???=int_0^(2pi) abs(F_(t theta))^2+abs(F_(theta theta))^2+pt_theta (A(nd F,nd F))dot.c F_theta dd(theta)) \
    &>=int_0^(2pi)abs(F_(theta theta))^2-abs(A)abs(nd F)^2 abs(F_(theta theta)) dd(theta) \
    &>=int_0^(2pi)3/4 abs(F_(theta theta))^2-abs(A)^2 abs(nd F)^4 dd(theta) \
    &>=int_0^(2pi)3/4 abs(F_(theta theta))^2-1/4 abs(F_theta)^2 dd(theta) quad "when" abs(nd F) "small"
  . $ Since $int_0^(2pi)F_theta dd(theta)=0$, 1-dimensional Poincaré inequality gives $
    int_0^(2pi)abs(F_theta)^2 dd(theta)<=int_0^(2pi)abs(F_(theta theta))^2 dd(theta)
  . $ Hence for $t>=T_0$ sufficiently large, $p''(t)>=p(t)$. Let $q(t)=p(t)e^t$, then  $
    q'(t)&=p'(t)e^t+p(t)e^t
  , $ and $ 
    q''(t)&=p''(t)e^t+p(t)e^t+2p'(t)e^t>=2p(t)e^t+2p'(t)e^t=2q'(t)
  . $ So $(q'(t)e^(-2t))'>=0$. If $q'(t)>0$ at some $T_1$, then $
    q'(t)>=e^(2(t-T_1))q'(T_1)
  . $ We will have $q(t)$ grows at at least $e^(2t)$. This contradicts to $p(t)->0$. Hence $q'(t)<=0$ and
  $p(t)<=p(T_0)e^(T_0-t)$.

  Now for $T_0<=a<b$, $
    norm(F_a-F_b)_(L^2)^2&=int_0^oo #h(-.4em)int_0^(2pi)abs(F(t+a)-F(t+b))^2 dd(theta)dd(t) \
    &<=abs(a-b)int_0^oo sup_([a,b])int_0^(2pi)abs(nd F)^2 dd(theta)dd(t) \
    &<=C e^(-a)
  . $ Hence $F_T$ converges in $L^2$ to a constant.

  We have obtained that $
    int_(t>=T)abs(nd F)^2 dd(theta)dd(t)=O(e^(-T))
  . $ Back to polar coordinate, this is $
    Eps(F|_(D(0,r)))=O(r)
  . $ Rescale $D(z,abs(z))$ to $D(2)$ and apply $eps$-regularity we get $
    abs(z)abs(nd F)=O\(abs(z)^(1/2-delta)\), forall delta>0
  . $ Hence $nd F in L^(2+delta)$ for some $delta>0$. This guarantees $u in C^(0,alpha)$.
]

== Weyl Tensor
Let $ 
  (A dot.circle B)_(i j k l)=A_(i l) B_(j k)+A_(j k)B_(i l)-A_(i k)B_(j l)-A_(j l)B_(i k)
. $ Define $
  W=R-1/(n-2)(Ric-S/n g)dot.circle g-S/(2n(n-1))g dot.circle g
, $ #ie $
  W_(i j k l)=R_(i j k l)&-1/(n-2)(g_(i l)R_(j k)+g_(j k)R_(i l)-g_(i k)R_(j l)-g_(j l)R_(i k)) \
  &+S/((n-1)(n-2)) (g_(i l)g_(j k)-g_(i k)g_(j l))
. $ The decomposition is orthogonal in the sense of $
  abs(R)^2:=R_(i j k l)R^(i j k l)
  =abs(W)^2+abs(1/(n-2)(Ric-S/n g)dot.circle g)^2+abs(S/(2n(n-1))g dot.circle g)^2
. $ $W$ has the same symmetry and Bianchi identities as $R$, while $W$ is totally trace free, #ie
$g^(i l)R_(i j k l)=0$.

For a 4-manifold
