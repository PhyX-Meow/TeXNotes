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
#show heading.where(level: 2): it => text(font: "Miama Nueva", it) + v(9pt)
= I. Geometry
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
Let $(M,g)$ be a Riemannian manifold with curvature tensor $R$, $ 
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
#theorem[
  $(M,g)$ is conformally flat if and only if $W==0$.
]

For a 4-manifold $M$, $Omega^2 (M)$ splits into self-dual and anti-self-dual parts $Omega^2_+ dsum Omega^2_-$,
which are $plus.minus 1$ eigenspaces of Hodge star "$op(*)$". Under an ONB, we have $
  Omega^2_+&=span{e_1 wed e_2+e_3 wed e_4,e_1 wed e_3-e_2 wed e_4,e_1 wed e_4+e_2 wed e_3} \
  Omega^2_-&=span{e_1 wed e_2-e_3 wed e_4,e_1 wed e_3+e_2 wed e_4,e_1 wed e_4-e_2 wed e_3}
. $ The curvature operator splits _w.r.t._ the direct sum as $
  cal(R)=mat(delim:"[",
    A,B;B^*,C
  )
. $ This gives a decomposition of $cal(R)$ by $
  cal(R)|-->(tr A,B,A-1/3 tr A,C-1/3 tr C)
, $ where $tr A=tr C=1/4 S$, $B$ is the traceless Ricci tensor, and last 2 components, denote by $W_+$ and
$W_-$, sum to the Weyl tensor $W=W_++W_-$

== Berger's inequality
#theorem[
  Suppose $(M,g)$ has sectional curvature bound $lambda<=K_sigma<=Lambda$, then for an ONB ${e_i}$, we have $
    abs(R_(i j k i))<=1/2(Lambda-lambda),quad abs(R_(i j k l))<=1/3 (Lambda-lambda)
  . $
]
#proof[
  Let $K(X,Y)=R(X,Y,Y,X)/(abs(X)^2 abs(Y)^2-pari(X,Y)^2)$, we have $
    lambda&<=K(e_i,b e_j+c e_k)&&<=Lambda \
    lambda&<=K(a e_i+b e_k,c e_j+d e_l)&&<=Lambda
  . $ For first inequality, note that $R_(i j k i)=R_(i k j i)$, we have $
    0&<=(R_(i j j i)-lambda)b^2+2R_(i j k i) b c+(R_(i k k i)-lambda)c^2 \
    0&<=(Lambda-R_(i j j i))b^2-2R_(i j k i) b c+(Lambda-R_(i k k i))c^2
  . $ Hence we see $abs(R_(i j k i))<=1/2 (Lambda-lambda)$. Then let $
    F(i,j,k,l)&=K(a e_i+b e_j,c e_k+d e_l)-lambda(a^2+b^2)(c^2+d^2) \
    G(i,j,k,l)&=1/2 lr((F(i,j,k,l)+F(i,-j,k,-l)),size:#16pt) \
    H(i,j,k,l)&=G(i,l,k,j)+G(-i,j,l,k) \
    &=A a^2c^2+B a^2d^2+C b^2c^2+D b^2d^2+2E a b c d
  , $ where $-i$ means $-e_i$ and $
    A&=R_(i k k i)+R_(i l l i)-2lambda & quad quad B&=R_(i j j i)+R_(i k k i)-2lambda \
    C&=R_(k l l k)+R_(j l l j)-2lambda & quad quad D&=R_(j l l j)+R_(j k k j)-2lambda \
    E&=3R_(i j k l)
  . $ View $H>=0$ as a quadratic polynomial in $a,b$ we see $
    0<=(A c^2+B d^2)(C c^2+D d^2)-(E c d)^2=A C c^4+(A D+B C-E^2)c^2 d^2+B D d^4
  . $ Divide by $c^2d^2$ and let $u=c^2\/d^2=sqrt(B D\/A C)$ we get $
    E^2<=A D+B C+A C u+B D u^(-1)=(sqrt(A D)+sqrt(B C))^2
  . $ Hence $
    abs(R_(i j k l))<= (sqrt(A D)+sqrt(B C))/3<=1/6 (A+B+C+D)
  . $ Similarly we have $
    Lambda(a^2+b^2)(c^2+d^2)-K(a e_i+b e_j,c e_k+d e_l)>=0
  . $ This gives $
    abs(R_(i j k l))<= (sqrt(A' D')+sqrt(B' C'))/3<=1/6 (A'+B'+C'+D')
  , $ where $
    A'&=2Lambda-R_(i k k i)-R_(i l l i) & quad quad B'&=2Lambda-R_(i j j i)-R_(i k k i) \
    C'&=2Lambda-R_(k l l k)-R_(j l l j) & quad quad D'&=2Lambda-R_(j l l j)-R_(j k k j)
  . $ Then we see $
    abs(R_(i j k l))<=1/6 (A+B+C+D+A'+B'+C'+D')=2/3 (Lambda-lambda)
  . $ 
]

#let ddot = math.dot.double
== 2nd variation of surface with boundary
Let $F_t:Sigma times (-eps,eps)->(M,g)$ where $Sigma$ is compact, smooth, with smooth boundary $pt Sigma$.
Write $nd$ for derivative and connection on $M$, $hat(nd)_V W=nd_V W-II(V,W)$ for the induced connection on
$Sigma$. Let $X=dot(F_t)|_(t=0),Z=ddot(F_t)|_(t=0)$, we have $
  lr(dv(,t)|)_(t=0) cal(A)(F_t)=int_Sigma div_Sigma X dd(mu_Sigma)
  =int_(pt Sigma)X dot.c nu dd(mu_(pt Sigma))-int_Sigma X dot.c H dd(mu_Sigma)
, $ where $dd(mu_Sigma)=sqrt(det pari(nd_i F,nd_j F)_g)dd(x)$ and $nu$ is the unit outer normal. Write $
  M_(i j) (t)=pari(nd_i F_t,nd_j F_t)_g
, $ we have Taylor expansion $
  dot(M)_(i j)(0)&=pari(nd_i X,nd_j F)+pari(nd_i F,nd_j X) \
  ddot(M)_(i j)(0)&=2pari(nd_i nd_t F,nd_j nd_t F)+pari(nd_t nd_i nd_t F,nd_j F)+pari(nd_i F,nd_t nd_j nd_t F) \
  &=2pari(nd_i X,nd_j X)+pari(nd_i Z,nd_j F)+pari(nd_i F,nd_j Z) \
  &#hide[=]+R(X,e_i,X,e_j)+R(X,e_j,X,e_i)
. $ Note that if we choose coordinate such that $F_i=e_i$ orthonormal, then $M_0=(delta_(i j))$, $
  dv(,t,2) det M_t=tr ddot(M)+(tr dot(M))^2-tr \(dot(M)^2\)
. $ We have $
  tr dot(M)&=2div_Sigma X, \
  tr ddot(M)&=2|hat(nd) X|^2+2div_Sigma Z-2R(X,e_i,e_i,X)
, $ $ 
  tr \(dot(M)\)^2&=2sum_(i,j) pari(nd_i X,e_j)^2+2sum_(i,j)pari(nd_i X,nd_j F)pari(nd_j X,nd_i F) \
  &=2|\(hat(nd) X\)^breb|^2+2sum_(i,j)pari(nd_i X,e_j)pari(nd_j X,e_i)
. $ Using the fact $(sqrt(u))''(0)=-1/4 u'(0)^2+1/2 u''(0)$ for $u(0)=1$, we have $
  lr(dv(,t,2)|,size:#24pt)_(t=0)cal(A)(F_t)&=int_(Sigma)1/2 tr ddot(M)+1/4 (tr dot(M))^2-1/2 tr \(dot(M)\)^2
  dd(mu_Sigma)\
  &=int_Sigma div_Sigma Z+(div_Sigma X)^2+|\(hat(nd) X\)^perp|^2 \
  &#hide[$=int_Sigma$]-sum_(i,j)pari(nd_i X,e_j)pari(nd_j X,e_i)-sum_i R(X,e_i,e_i,X)dd(mu_Sigma)
. $ More generally, if $F=F_(s,t)$, with variation field $X$ and $Y$, only need to replace $Z$ by $nd_X Y$.
Note that $nd_X Y-nd_Y X=[X,Y]=0$.

If $Sigma=gamma$ is 1-dimensional, #ie a geodesic, the formula reduces to $
  &lr(dv(,t,2)|,size:#24pt)_(t=0)cal(L)(F_t) \
  &=int_(pt gamma) Z dot.c nu (dd(\#))
  +int_gamma |\(hat(nd) X\)^perp|^2-R(X,gamma',gamma',X)dd(ell) \
  &=int_(pt gamma) Z dot.c nu (dd(\#))
  +int_gamma pari(nd_(gamma')X,nd_(gamma')X)-pari(nd_(gamma')X,gamma')^2-R(X,gamma',gamma',X)dd(ell) \
  &=int_(pt gamma) Z dot.c nu+X dot.c nd_nu X (dd(\#))
  -int_gamma pari(nd_(gamma')nd_(gamma')X+R(X,gamma')gamma',X)+pari(nd_(gamma')X,gamma')^2 dd(ell)
. $ For a geodesic net with smooth $X$, there are only the interior terms, #ie $
  lr(dv(,t,2)|,size:#24pt)_(t=0)cal(L)(F_t)=int_gamma |\(nd_(gamma')X\)^perp|^2-R(X,gamma',gamma',X)dd(ell)
. $ If we choose the variation be "moving nodes", then $X$ can be chosen to be Jacobi, #ie $
  nd_(gamma')nd_(gamma')X+R(X,gamma')gamma'=0
. $ Then we have $
  nd_(gamma')pari(nd_(gamma')X,gamma')=pari(nd_(gamma')nd_(gamma')X,gamma')+pari(nd_(gamma')X,H)=0
. $ Hence $pari(nd_(gamma')X,gamma')=nd_(gamma')pari(X,gamma')$ is a constant. We get $
  lr(dv(,t,2)|,size:#24pt)_(t=0)cal(L)(F_t)=int_(pt gamma) Z dot.c nu+X dot.c nd_nu X (dd(\#))
  -int_gamma pari(nd_(gamma')X,gamma')^2 dd(ell)
. $ Note that $Z$ takes the same value at a node whichever string we view from, but $nd_nu X$ may not be 
addable in $nu$.

#example[
  Suppose $M$ is the round 2-sphere, $Sigma$ is a geodesic net consists of nodes ${P_i}$ and strings
  $\{gamma_j:P_(a_j)->P_(b_j)\}$, the formula reduces to $
    I(X,X)=-1/2 sum_(gamma:P_i->(dot.c))nd_(gamma')abs(X)^2
    -sum_j lr((nd_(gamma'_j)pari(X,gamma'_j)),size:#14pt)^2 ell_j
    =sum_j (\(A_j^2+B_j^2\)cos ell_j-2A_j B_j)/(sin ell_j)
  , $ where $ell=cal(L)(gamma_j),A_j=X dot.c gamma'_j (0),B_j=X dot.c gamma'_j (ell_j)$.
]









#pagebreak()
= II. Analysis
