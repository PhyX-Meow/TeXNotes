#import "@phyxmeow/preamble:0.1.0": *
#show: preamble.with(
  font: "xcharter",
  numbering: "1.1.",
)

#align(center)[#text(20pt)[
  *Leon Simon's Geometric Measure Theory*
]#v(0.5cm)]

#let dH(n) = $dd(cal(H)^n)$
#let spt = math.op("supp")
#let Vol = math.op("Vol")

= Preliminary
- Measure theory: Egorov's thm, Lusin's thm, Hausdorff measure, Lebesgue
  density theorem, covering lemma...

#theorem(name:"Comparison")[
  Suppose $mu,mu_0$ are open $sigma$-finite Borel regular measures on metric
  space $X$, and $mu_0$ has Symmetric Vitali Property. Let $A cc X$ (may not be
  measurable), then $
    Theta^(*mu_0)(mu,x)>=lambda forall x in A=>mu(A)>=lambda mu_0 (A)
  . $
] <comparison>

#theorem(name:"Upper Density")[
  If $mu$ is a Borel regular measure on metric space $X$ and $A$ is a
  $mu$-measurable set with *finite measure*. Then $
    Theta^(*n)(mu,A,x)=0 "for" cal(H)^n"-a.e." x in X\\A
  . $ Where $Theta^(*n)$ is the upper density with respect to $cal(H)^n$.
  Specially for $X=RR^n$, the density can be defined, and further $
    Theta^(n)(mu,A,x)=1 "for a.e." x in A "and"
    Theta^(n)(mu,A,x)=0 "for a.e." x in.not A
  . $
] <upper-density>

#theorem(name:"Radon-Nikodym")[
  Suppose $mu,mu_0$ Borel regular and open $sigma$-finite on metric space $X$,
  $mu_0$ has the Symmetric Vitali Property, then
  + If $mu$ is absolutely continuous w.r.t $mu_0$, then #h(1fr) $
    mu(A)=int_A Theta^(mu_0)(mu,x)dd(mu_0(x)), forall A cc X "Borel".
  $ 
  + Without assuming absolutely continuous, we still have $
    mu(A)=int_A Theta^(mu_0)(mu,x)dd(mu_0(x))+lr(mu|)_(Z)(A),
    forall A cc X "Borel",
  $ where $Z$ is a $mu_0$-null Borel set.
  + If $mu$ also has the Symmetric Vitali Property, then $
    Z={x in X:Theta^(mu_0)(mu,x)=oo} 
  . $
]

== Area and Co-area formula
This is the measure theoretical generalization of area of a submanifold.
#theorem[
  Let $U cc RR^n$ open, $f:U->RR^m$ locally Lipschitz. Let $
  cal(J)_f=cases(
    sqrt(det(dd(f)dd(f)^T)) #h(2em) & n<=m\,,
    sqrt(det(dd(f)^T dd(f))) & n>=m.
  ) $ Then for any $A cc U$ Lebesgue measurable, we have $
  int_A cal(J)_f dd(x)=cases(
    display(int_(RR^m)cal(H)^0 (A sect f^(-1)(y))dd(cal(H)^n (y)) & n<=m\,),
    display(int_(RR^m)cal(H)^(n-m) (A sect f^(-1)(y))dd(cal(H)^m (y))
      #h(2em) & n>=m.)
  ) $ Further, if $u:A->[0,oo]$ measurable, we have $
  int_A u cal(J)_f dd(x)=cases(
    display(int_(RR^m)sum_(x in f^(-1)(y))u(x)dd(cal(H)^n (y)) & n<=m\,),
    display(int_(RR^m)int_(f^(-1)(y))u(x)dd(cal(H)^(n-m)(x))dd(cal(H)^m (y))
      #h(2em) & n>=m.)
  ) $
]
#remark[
  More generally, we may have $A cc M cc RR^(n+k)$, where  $M$ is an $n$
  dimensional submanifold of $RR^(n+k)$. Then the formula still holds if $dd(x)$
  is replaced by $dd(cal(H)^n)$.
]

#theorem(name: [$C^1$ Sard-type Theorem])[
  Let $M$ be an $n$ dimensional $C^1$-manifold, $m<=n$, $f:M->RR^m$ be $C^1$.
  Then for a.e. $y in f(M)$, $f^(-1)(y)$ can be decomposes as $
    (f^(-1)(y)\\ C) union (f^(-1)(y)sect C)
  , $ where $C={x in M:rank dd(f)<m}={cal(J)_f=0}$, $f^(-1)(y)\\C$ is a
  $(n-m)$-dimensional embedded $C^1$-submanifold and $cal(H)^(n-m)(f^(-1)(y)
  sect C)=0$.
]
#remark[
  The classical Sard's Theorem asserts that if $M$ and $f$ are $C^(n-m+1)$,
  then for a.e. $y$, $f^(-1)(y)sect C$ is actually empty.
]

#proposition(name: [Intrinsic proof of Divergence Theorem])[
  For a compactly supported vector field $X$ on $M$, let $vphi(t,x)$ be its flow,
  note that $
    int_M div X dd(cal(H)^n)
    =lr(dv(,t)|)_(t=0)int_(M) cal(J)_(vphi_t)dd(cal(H)^n)
    =lr(dv(,t)|)_(t=0)cal(H)^n (vphi_t (M))=0
  . $
]

== First and second variation of area

Recall for $C^2$ manifolds in $RR^(n+k)$, we can define its 2nd fundamental
form $
  B(X,Y)=hat(nd)_X iota_* Y-iota_* nd_X Y=-(hat(X) dot.c hat(nd)_Y nu_alpha)
  nu_alpha, quad (nu_alpha "ONB of normal bundle")
. $ And the mean curvature is defined by $
  H=tr_g B=sum_i B(e_i,e_i)=-sum_alpha (div_M nu_alpha) nu_alpha
. $

We can now calculate the 1st variation of a submanifold. Suppose the variation
has compact support, denote it by $vphi_t$ and $lr(X=dv(,t)|)_(t=0)vphi_t$.
By area formula, we have (locally): $
  cal(H)^n (vphi_t (M))=int_M cal(J)_(vphi_t)dd(cal(H)^n)
. $ So $
  lr(dv(,t)|)_(t=0) cal(H)^n (vphi_t (M))=int_M div_M X=
  int_M div_M X^perp+div_M X^breb
. $ Note that $
  div_M X^perp=0,quad div_M X^breb=sum_i nd_(e_i) X^breb dot.c e_i
  =-X^breb dot.c sum_i nd_(e_i) e_i=-X dot.c H
. $ Hence $
  lr(dv(,t)|)_(t=0) cal(H)^n (vphi_t (M))=-int_M X dot.c H dd(cal(H)^n)
. $
#remark[
  - If $M$ has a boundary, then we get #h(1fr) $
      int_M div_M X dd(cal(H))^n=-int_M X dot.c H dd(cal(H)^n)-int_(pt M)
      X dot.c eta dd(cal(H)^(n-1))
    . $ Where $eta$ is the unit outer normal of the boundary.
  - If the 1st variation is identically zero, we call $M$ #emph[stationary].
]

Then we calculate the 2nd variation, let $
  Z=lr(pdv(vphi(t,x),t,2)|)_(t=0), quad \("recall" X=lr(pdv(vphi(t,x),t)|)_(t=0))
. $ Then we have Taylor expansion $
  vphi_t (x)=x+t X+1/2 t^2 Z+o\(t^2)
. $ Then $
  nd_(e_i)vphi_t x=e_i+t nd_(e_i)X+t^2/2 nd_(e_i)Z+o\(t^2)
. $ So the metric is $
  g_(t;i j)=nd_(e_i)vphi_t dot.c nd_(e_j)vphi_t
  =delta_(i j)&+t (e_i dot.c nd_(e_j)X+e_j dot.c nd_(e_i)X) \
  &+t^2/2 (e_i dot.c nd_(e_j)Z+e_j dot.c nd_(e_i)Z+2nd_(e_i)X dot.c nd_(e_j)X) \
  &+o\(t^2)
. $ Then by $
  det(I+A)=1+tr A+1/2 (tr A)^2-1/2 tr (A^2)+O(abs(A)^3)
, $ $
  det g_t&=1+2t div_M X+t^2
  (div_M Z&&+sum_i abs(nd_(e_i)X)^2+2(div_M X)^2 \
  & &&-1/2sum_(i j)(e_i dot.c nd_(e_j)X+e_j dot.c nd_(e_i)X)^2)+o\(t^2\) \
  &=1+2t div_M X+t^2
  (div_M Z&&+sum_i abs((nd_(e_i)X)^perp)^2+2(div_M X)^2 \
  & &&-sum_(i,j)(e_i dot.c nd_(e_j)X)(e_j dot.c nd_(e_i)X))+o\(t^2\)
. $ Finally $
  cal(J)_(vphi_t)=sqrt(det g_t)=1+t div_M X+t^2/2
  (div_M Z&+(div_M X)^2+sum_i abs((nd_(e_i)X)^perp)^2\
  &-sum_(i,j)(e_i dot.c nd_(e_j)X)(e_j dot.c nd_(e_i)X))+o\(t^2)
. $ As a result, for a stationary $M$, $X in N M=T M^perp$ $
  lr(dv(,t,2)|)_(t=0)cal(H)^n (vphi_t (M))=int_M
  sum_i abs((nd_(e_i) X)^perp)^2-sum_(i,j)(X dot.c B\(e_i,e_j\))^2 dd(cal(H)^n)
. $ In particular, if $k=1$, #ie $M$ has codimension 1, then $
  lr(dv(,t,2)|)_(t=0)cal(H)^n (vphi_t (M))=int_M
  abs(nd^M u)^2-u^2 abs(B)^2 dd(cal(H)^n)
. $ Where $x=u nu$, $nu$ is the unit normal.
#remark[
  If the background manifold is not $RR^(n+k)$, there will be a curvature term
  in addition.
]

#proposition[
  The Simon's cone $
  {(x^1)^2+(x^2)^2+(x^3)^2+(x^4)^2=(x^5)^2+(x^6)^2+(x^7)^2+(x^8)^2}cc RR^8
  . $ is stationary and stable.
]

== BV functions
#let BV = math.op("BV")
#let supp = math.op("supp")
#definition[
  Let $u in L_"loc"^1 (U), U cc RR^n$, $u$ is said to be locally bounded
  variation, #ie $in BV_"loc"$, if for any $K cc cc U$ compact and
  $X=X^i pdv(,x^i) in C_0^oo (K)$, $
    int_K u div X dH(n)<=C(K)norm(X)_(L^oo)
  . $
]
Note that this means $
  X|->int_K u div X dH(n)
$ Extends (uniquely) to a linear functional on $C_0 (U,RR^n)$ which is
bounded when restricted to $C_0 (K,RR^n)$.

By Riesz Representation Theorem, there is a Radon measure $mu$ and a Borel
measurable vector function $v$, $abs(v)=1$ a.e. such that $
  int_U u div X dH(n)=int_U X dot.c v dd(mu)
. $ #ie $nd u = v dd(mu)$ in the distribution sense. If $u in W^(1,1)$, then
we have $
  v_i=(nd_i u)/(abs(nd u)), quad "and " dd(mu)=abs(nd u)dH(n)
. $ From above, for any $W cc U$ open, $
  mu(W)=sup_(X "Lip",abs(X)<=1,supp X cc K) int_W u div X dH(n)
. $ We use $abs(nd u)$ for Radon measure $mu$ in later discussions.

#lemma(name:"Mollify BV functions")[
  Let $vphi_eps$ be a family of our favorite kernels, $u in BV_"loc" (U)$, then
  $u_eps=u*vphi_eps->u$ in $L_"loc"^1$ and $abs(nd u_eps)->abs(nd u)$ as
  Radon measures.
]

#theorem(name:"Compactness of BV functions")[
  Suppose ${u_k}cc BV_"loc" (U)$ and for any $K cc cc U$, $
    norm(u_k)_(W^(1,1)(K))=norm(u_k)_(L^1 (K))+int_K abs(nd u_k)dH(n)<=C=C(K)
  . $ Then there is a subsequence ${u_k'}$ such that $u_k'->u$ in $L_"loc"^1$
  and for any $K cc cc U$, $
    int_K abs(nd u)<=liminf int_K abs(nd u_k')
  . $ #ie $u_k'->u$ in $W^(1,1)$-weak sense.
]
By above characterization of $abs(nd u)$, the inequality on derivative is easy
to see once we have $u_k' xarrow(L^1)u$. Also using diagonal argument, only need
to prove the existence of $L^1$ convergent subsequence on every compact $K cc U$.
This is true by the following:
#proof[
  Suppose $A cc BV_"loc" (U)$, bounded in $W^(1,1)$ norm on every compact $K$.
  For $u in A$, let $u_eps$ be $phi_eps * u$, then $
    abs(u_eps (x))&<=int_(B(0,eps))vphi_eps (y)abs(u(x-y))dd(y)
    <=eps^(-n)norm(vphi_1)_(L^oo)norm(u)_(L^1) \
    abs(nd u_eps (x))&=int_(B(0,eps))(nd vphi_eps) (x-y)u(y)dd(y)
    =int_(B(0,eps))(nd vphi_eps)(y)u(x-y)dd(y) \
    &<=eps^(-n-1)norm(nd vphi_1)_(L^oo)norm(u)_(L^1)
  . $ So ${u_eps:u in A}$ is uniformly bounded and equicontinuous, therefore
  precompact in $C^0(K)$, and then also in $L^1(K)$. Then consider for $u$
  smooth $
    abs(u-u_eps)&<=int_(B(0,eps))vphi_eps (y)abs(u(x)-u(x-y))dd(y) \
    &<=int_(B(0,eps))vphi_eps (y)int_0^(eps abs(y))abs(pt_r u(x-r v))dd(r)dd(z),
    quad v=y/abs(y)
  . $ Hence $
    norm(u-u_eps)_(L^1)<=eps int_K abs(nd u)
  . $ For $u$ non-smooth we can use smooth approximation.
]
#let ni = math.in.rev
#theorem[
  Suppose $U ni 0$ is bounded, open and convex, let $delta$ be such that
  there is $R>0$ such that $B(0,delta R)cc U cc B(0,R)$. Suppose $u in BV(U)$,
  then for any $theta in (0,1)$ and any $c in RR$ #st $
    m({u(x)>=c})>=theta m(U),quad "and"quad m({u(x)<=c})>=theta m(U)
  . $ Then $
    int_U abs(u-c) dH(n)<=C R int_U abs(nd u),quad C=C(theta,delta,n)
  . $ <BV-poincare>
]
#proof[
  WLOG assume $R=1$, choose a convex $W cc U$ such that $
    int_W abs(u-c)dH(n)>=1/2 int_U abs(u-c)dH(n)
  $ and the $theta$-condition holds for $(W,theta/2)$ in place of $(U,theta)$.
  (We may choose $W={d(x,pt U)>eps}$ for $eps$ small enough). Let
  $u_eps=u*vphi_eps$. For $eps$ small, we have the $theta$-condition for
  $u_eps$ on $(W,theta/4)$. Then by usual Poincaré inequality we have $
    int_W abs(u_eps-c_eps)dH(n)<=C int_W abs(nd u_eps)dH(n),quad
    C=C(n,theta,delta),
  $ for suitable $c_eps->c$ and any $eps$ small enough. Let $eps->0$ we get
  the desired inequality.
]

#theorem[
  $U,delta,R$ same as last theorem, suppose $u in BV(RR^n)$ with $supp u cc
  bar(U)$. Then $
    int_(RR^n)abs(nd u)=int_(bar(U))abs(nd u)<=C(int_(U)abs(nd u)+
    1/R int_U abs(u)dH(n))
  . $ Combine this with last theorem we conclude $
    1/R int_(RR^n)abs(u-c Id_U)+int_(RR^n)abs(nd(u-c Id_U))<=
    C int_U abs(nd u)
  . $
]

= Rectifiable Sets and Varifolds
== Countably $n$-rectifiable sets
#definition[
  A set $M cc RR^(n+k)$ is said to be _countably_ $n$_-rectifiable_ if $
    M cc M_0 union (union.big_(j=1)^oo f_j (RR^n))
  , $ where $cal(H)^n (M_0)=0$, $f_j:RR^n->RR^(n+k)$ Lipschitz.
  This equivalent to say $
    M cc M_0 union (union.big_(j=1)^oo f_j (A_j))
  , $ where $cal(H)^n (M_0)=0$, $A_j cc RR^n$, $f_j:A_j->RR^(n+k)$ Lipschitz. \
  In rough words, $M$ is almost everywhere a countably union of $n$-dimensional
  pieces.
]

#h(-2em)
*Examples:*
- Almost everywhere $n$-dim manifolds.
  - with boundaries and corners.
  - with self-intersections.
- Union of every rational line (#ie line passing through at least 2 rational
  points) on $RR^2$ is countably 1-rectifiable.
  - Terrible example!
- ?The 2-dimensional Cantor dust $C times C$ is not 1-rectifiable.

#lemma[
  $M$ is countably $n$-rectifiable if and only if $
    M cc N_0 union (union.big_(j=1)^oo N_j)
  , $ where $N_j$ are $n$-dim embedded $C^1$-submanifolds.
]
#proof[
  "$arrow.double.l$" is trivial since a $C^1$-manifold is countably union
  of Lip (and actually $C^1$) images.

  "$=>$" is true by approx a Lip function $f_j$ by $h_(j k)$ #st $
    cal(H)^n ({f_j!=h_(j k)})<1/2^k
  . $ Note that Lip functions maps null set to null set. We still need to prove
  the image of $h_(j k)$ is almost countably many embedded $C^1$-submanifolds.
  By co-area formula, the set of critical values is measure zero and the regular
  points can be covered countably by good charts.
]

#definition[
  Let $M cc RR^(n+k)$ be $cal(H)^n$-measurable, let $p in M$, we say a $n$-dim
  affine subspace $W$ through $p$ is the approximate tangent space of $M$ at
  $p$ if $
    lim_(eps->0)lr(cal(H)^n|)_(1/eps (M-p))-->lr(cal(H)^n|)_(W-p) "as measures".
  $ #ie the submanifold measure converges to the measure on the tangent plane
  if we zoom in at $p$. This $W=T_p M$ is unique if exist.
]

- #text(blue)[What is the tangent space of union of rational lines?]
- #text(red)[They don't exist.]

#remark[
  Let $f_eps:RR^(n+k)->[0,1]$ be $C^1$ and radical that is 1 on $B(0,1)$ and
  supported on $B_(0,1+eps)$. Suppose $T_x M$ exists, we see $
    lim_(r->0) 1/(omega_n r^n) cal(H)^n (M sect B(x,r))=1
  . $ #ie $lr(cal(H)^n|)_(M)$ has density 1 at $x$ with respect to $cal(H)^n$.

  Similarly, $
    lim_(r->0) 1/(omega_n r^n) cal(H)^n (M sect {v in T_x RR^(n+k):
    d(v,(T_x M)^perp)<=alpha |v|}sect B(x,r))=0
  . $
]

#theorem[
  Suppose $M cc R^(n+k)$ is $cal(H)^n$ measurable and has locally finite
  measure. Then $M$ is countably $n$-rectifiable $iff T_x M$ exists
  $cal(H)^n$-#emph[a.e.] on $M$
] <rect-criterion>
#proof[
  "$=>$": We may write $M$ as disjoint union $M_0union union.big_j^oo M_j$ where
  $cal(H)^n (M_0)=0$ and $M_j cc N_j$, $N_j$ embedded $C^1$-submanifolds. Let
  $f in C^0 (RR^(n+k))$ be supported on $B(0,R)$. Note that $
    M union (N_j \\ M)=N_j union (M \\ N_j)
  . $ Let $lambda_(x,eps)(y)=1/eps (y-x)$, then $
    int_(lambda_(x,eps)(M))f dH(n)=int_(lambda_(x,eps)(N_j))f dH(n)
    -int_(lambda_(x,eps)(N_j\\M))f dH(n)+int_(lambda_(x,eps)(M\\N_j))f dH(n)
  . $ Suppose $x in M_j cc M sect N_j$, since $N_j$ is a manifold, the first
  term gives the classical tangent space $T_x N_j$. Then by the upper density
  theorem, since $x in.not N_j\\M$ and $M\\N_j$, the other terms tends to $0$.
  Hence $T_x M$ exists and equal to $T_x N_j$ for $cal(H)^n$-a.e. $x in M_j$.
  Note that $M$ has finite measure on every compact set is essential for
  the density theorem.

  "$arrow.double.l$": WLOG assume $cal(H)^n (M)>0$ and $M cc B(0,R)$. For any
  subspace $W cc RR^(n+k)$, $alpha in (0,1)$, define the double cone $
    Gamma_alpha (W,x)={y in RR^(n+k):abs(v-pi_W (v))<=alpha abs(v),v=y-x}
  . $ And define the distance between $W,W'$ by $
    d(W,W')=sup_(abs(v)=1) abs(pi_W (v)-pi_(W')(v))
  . $ (In fact $d(W,W')=norm(pi_W-pi_(W'))$ as operators).

  By the remark above, for any $x in B(0,R)$ where $T_x M$ exists, $
    lim_(r->0) mu(B(0,r))/(omega_n r^n)=1,quad "where" mu=lr(cal(H)^n|)_(M)
  , $ and $
    lim_(r->0) mu(Gamma_alpha (N_x M,x)sect B(0,r))/(omega_n r^n)=0,quad
    "where" N_x M=(T_x M)^perp
  . $ Define $
    theta_j=inf_(0<r<1/j)mu(B(0,r))/(omega_n r^n),quad
    eta_j=inf_(0<r<1/j)mu(Gamma_alpha (N_x M)sect B(0,r))/(omega_n r^n)
  . $ Then $lim_j theta_j=1$, $lim_j eta_j=0$ for $mu$-a.e. $x in M$. Hence
  by Egorov's theorem, we can choose a Borel $E cc M$ with $mu(E^c)$ small
  such that $theta_j,eta_j$ converge uniformly on $E$.

  Fix $alpha=1/2$, choose $k$-dim subspaces $W_1,...,W_m$ that form a $eps$-net
  of $op("Gr")(n+k,k)$, and let $
    E_j={x in E:d(W_j,N_x M)<eps}
  . $ Then $E=union.big_(j)^m E_j$. Choose $N$ such that for $x in E$, $j>=N$, $
    theta_j (x)>=1-eps^(n+1),quad eta_j (x)<=eps^(n+1)
  . $ We #underline[claim]: $
    Gamma_(alpha/2)(W_j,x)sect E_j sect B lr((x,1/(2N)),size:#50%)={x},
    " "forall x in E_j,j=1,...,m
  . $ Otherwise if there is $x$ and $y in Gamma_(alpha/2)(W_j,x)sect E_j sect
  B(x,1/(2N))$, let $r=abs(y-x)<1/(2N)$, we have $
    mu lr((Gamma_(alpha/2)(W_j,x)sect B lr((x,1/N),size:#50%)),size:#75%)
    <=eps^(n+1) omega_n (2r)^n
  . $ On the other hand if $abs(z-y)<delta abs(y-x)$ small, we have $
    d(z-x,N_x M)&<delta abs(y-x)+d(y-x,N_x M)=delta+abs((y-x)-pi_(N_x M)(y-x)) \
    &<=delta abs(y-x)+abs((y-x)-pi_(W_j)(y-x))
      -abs(lr((pi_(N_x M)-pi_(W_j)),size:#75%) (y-x)) \
    &<=lr((delta+alpha/2+eps),size:#50%)abs(y-x)
  . $ Since $abs(y-x)<=abs(y-z)+abs(z-x)<=delta abs(y-x)+abs(z-x)$, we have $
    abs(y-x)<=1/(1-delta) abs(z-x)
  . $ So $
    d(z-x,N_x M)<= (delta+alpha/2+eps)/(1-delta) abs(z-x)<alpha abs(z-x)
  . $ #ie $B(y,delta r)cc Gamma_alpha (N_x M,x)sect B(x,1/N)$. Then $
    mu lr((Gamma_(alpha/2)(W_j,x)sect B lr((x,1/N),size:#50%)),size:#75%)
    >=mu(B(y,delta r))=omega_n delta^n r^n
  . $ This gives $
    eps (2 eps)^n>=delta^n
  . $ We can choose $delta=2eps$, this is a contradiction. The claim is proved.

  Take any $x_0 in E_j$ fixed, note that $x in B(x_0,1/(4N))cc B(x,1/(2N))$ for
  any $x in B(x_0,1/(4N))$. So we have $
    Gamma_(alpha/2)(W_j,x)sect E_j sect B lr((x_0,1/(4N)),size:#50%)={x},
    " "forall x in E_j sect lr((x_0,1/(4N)),size:#50%),j=1,...,m
  . $ This shows that $E_j$ can be written locally as a graph of a Lipschitz
  function $W_j->W_j^perp$ with Lip constant $alpha/2$ in $B(x_0,1/(4N))$.
  Since $j in {1,...,N}$ and $x_0 in E_j$ are arbitrary we can cover $E$
  by finitely many such small neighborhoods. We may choose $E$ such that
  $mu(M\\E)<1/2 mu(M)$ Then $mu(M\\"\"union of Lip graphs\"")<1/2 mu(M)$.
  Repeat these argument, we see $M$ is countably $n$-rectifiable. For general
  $M$, we may cover $M$ by countably many balls.
]

== Gradients, Jacobians, Area, Co-Area
For $M cc RR^(n+k)$ $n$-rectifiable, write $
  M=union.big_(j=0)^oo M_j,quad cal(H)^n (M_0)=0, M_i sect M_j=OO,i!=j,quad
  "and" M_j cc N_j,j>=1
, $ where $M_j$ are $cal(H)^n$-measurable and $N_j$ are $n$-dimensional
embedded $C^1$-submanifolds with $cal(H)^n \(N_j)<oo$. We define the tangent
plane of $x in M_j$ to be $T_x N_j$ (only $cal(H)^n$-a.e.). Note that this
definition works for non-locally finite $M$. Then for $f:U->RR^m$ locally Lip,
$U supset M$ open, $
  nd^M f=sum_i nd_(e_i)f(x) e_i,quad {e_i} "ONB of" T_x M
$ exists $cal(H)^n$-a.e.

We can then define the Jacobian of $f:M->RR^m$. The area and co-area formula
still hold for $f$ word-by-word. The slices $M sect f^(-1)(y)$ are countably
$(n-m)$-rectifiable subsets of $RR^(n+k)$ for a.e. $y in RR^m$. This is true
from the decomposition $M=union_(j=0)^oo M_j$ and $C^1$ Sard-type theorem and
the $C^1$ approximation theorem.
#theorem[
  For $f:RR^n->RR$ Lip, then there is $f_eps in C^1$ such that $
    m({f!=f_eps}union{nd f!=nd f_eps})<eps
  . $ If $W cc RR^n$ is closed and $f:C->RR,V:C->RR^n$ are continuous, suppose
  for each $K cc W$ compact, $
    lim_(y in K, y->x) (f(x)-f(y)-V(x)dot.c (x-y))/abs(x-y)=0,quad
    "uniformly in" x in K
  . $ Then there exist an extension $f:RR^n->RR$ such that $nd f=V$ on $C$.
]

Suppose $M_i$ is $n_i$-rectifiable subset of $RR^(n_i+k_i)$, write $M_i=
union_(j>=0) M_(i j)$, as above. Let $tilde(M)_i=union_(j>0) M_(i j)$, then we
have $
  tilde(M)_1 times tilde(M)_2=union.big_(j,l>0)M_(1 j)times M_(2 l)
. $ This is a countably $n$-rectifiable subset of $RR^(n+k)$, $n=n_1+n_2,k=k_1+
k_2$, and $
  cal(H)^n (tilde(M)_1 times tilde(M)_2)=cal(H)^(n_1)(M_1)cal(H)^(n_2)(M_2)
. $ Note that this may not be true if we use $M_i$ instead of $tilde(M)_i$.

== Purely unrectifiable sets
#definition[
  $S cc RR^(n+k)$ is called _purely_ $n$-_unrectifiable_ if $S$ contains
  no countably $n$-rectifiable subset with positive $cal(H)^n$ measure.
]
#lemma[
  If $A cc RR^(n+k)$ is $cal(H)^n$ $sigma$-finite, #ie $A=union_j A_j$ where
  the outer measure $cal(H)^n \(A_j)<oo$. Then $A$ is decomposed by $
    A=R union P
  , $ where $R$ is countably $n$-rectifiable and $P$ is purely $n$-unrectifiable.
  $R$ can be chosen Borel if $A$ is $cal(H)^n$-measurable.
]
#proof[
  If $A$ is $cal(H)^n$-measurable, we can choose $A_j$ above to be also
  measurable. Then there is $B_i cc A_i$ Borel such that $cal(H)^n (A_i\\B_i)=0$.
  Then let $
    alpha_i=sup{cal(H)^n (M):M cc B_i "countably" n"-rectifiable Borel set"}
  . $ Hence for each $i$, there is $R_(i j) cc C_i$ such that $
    cal(H)^n \(R_(i j))>alpha_i-1\/i
  . $ Then $R_i=union_i R_(i j)$ is countably $n$-rectifiable, Borel, and
  $B_i\\R_i$ is purely unrectifiable. Choose $R=union_i R_i$, $P=A\\R$.

  For $A$ not necessarily measurable, choose $B_j supset A_j$ such that $B_j$
  has the same $cal(H)^n$ (outer) measure as $A_i$. Let $B=union_j B_j$,
  $B=R union P$ as above. Then $A=(A sect R)union (A sect P)$ is a decomposition
  of $A$.
]

#lemma[
  $A cc RR^(n+k)$, may not be $cal(H)^n$-measurable, is purely $n$-unrectifiable
  if the orthogonal projection of $A$ onto every $n$ coordinates is an
  $cal(H)^n$-null set.
]
#proof[
  Easy to see contradiction if it contains a piece of positive measure on a
  $n$-dim submanifold.
]
#remark[
  This shows that the Cantor dust of any parameter is purely $1$-unrectifiable,
  though it may be Hausdorff 1-dimensional.
]

A more precise characterization is state as follows:
#theorem(name:"The Structure Theorem")[
  Suppose $Q cc RR^(n+k)$ is purely $n$-rectifiable and $cal(H)^n$
  $sigma$-finite. Then the orthogonal projection of $Q$ is $cal(H)^n$-null on
  a.e. $W < RR^(n+k)$ $n$-dim subspaces.
]

We omit the "countably" prefix for $n$-rectifiable sets from now.

== Sets of locally finite perimeter
Let $U cc RR^(n+1)$ open and $E$ (Lebesgue-)measurable. We say $E$ has _locally
finite perimeter_ in $U$ if $Id_E$ is $BV_"loc" (U)$. This is to say there is
a Radon measure $mu_E=abs(nd Id_E)$ and a Borel measurable a.e. unit vector $nu$ 
such that for any $X in C_0^1$, $
  int_(E sect U)div X=-int_(U)X dot.c nu dd(mu_E)
. $ If $E$ is an open submanifold, then the divergence theorem gives $
  mu_E=lr(cal(H)^n|)_(pt E sect U)
. $ Where $nu$ is the inward unit normal of $pt E$. Thus $mu_E$ can be viewed
as the generalized boundary measure.

Then, the _reduced boundary_ $pt^* E$ is defined by $
  pt^* E={x in U:lim_(r->0)(int_(B(x,r))nu dd(mu_E))/(mu_E (B(x,r))) "exists"
  "and has length 1"}
. $ Let $
  nu_E (x)=lim_(r->0)(int_(B(x,r))nu dd(mu_E))/(mu_E (B(x,r))
. $ Then $nu_E=nu$ $mu_E$-a.e. Hence $mu_E=lr(mu_E|)_(pt^* E)$.

#example[
  Let $q_1,q_2,...$ be every rational points in the closed unit disk, let $
    D_k=overline(B)(q_i,r_0/2^k) "and" A=union.big_k D_k
  . $ Then $A$ has locally finite perimeter because partial sum of the total
  variation of the sets are bounded. And a sequence of $BV$ functions has to
  converge (in $L^1$) to some limit. Then the limit has to be $Id_A$ because
  the sequence converges monotone and pointwise to it. But the topological
  boundary of $A$ is at least the whole disk. Even the boundary of the union
  of boundaries of $D_k$ contains the whole disk. But $pt^*A$ is somehow the
  actual "boundary" as we expected, and is countably 1-rectifiable.
]
#theorem[
  Suppose $E$ has locally finite perimeter in $U$, then $
    mu_E=lr(cal(H)^n|)_(pt^*E)
  . $ Further, $pt^*E$ is countably $n$-rectifiable and the approximate tangent
  space are given by $
    T_x pt^*E={nu_E (x)^perp}
  . $ Also, $nu_E (x)$ is the "inward pointing unit normal" of $E$ in the sense $
    forall x in pt^*E,quad 1/lambda (E-x)#xarrow[$L_"loc"^1$]{w:w dot.c nu_E>0}
  . $ 
]
#proof[
  WLOG assume $0 in pt^*E$ and $nu_E (0)=e_(n+1)$. Then since $
    nu_(n+1)<=abs(nu_(n+1))<=1,quad abs(nu_i)<=sqrt(1-nu_(n+1)^2)
    <=sqrt(2)sqrt(1-abs(nu_(n+1)))
  , $ we have $
    lim_(r->0)(int_(B(0,r))abs(nu_(n+1))dd(mu_E))/(mu_E (B(0,r)))=1,quad
    "and" quad lim_(r->0)(int_(B(0,r))abs(nu_(i))dd(mu_E))/(mu_E (B(0,r)))=0
  . $ For $eta in C_0^1 (U)$, support on $B(0,r) cc U$, $
    int_U nu_(n+1)eta dd(mu_E)=-int_U Id_E nd_(n+1)eta dd(x)
    <=int_E abs(nd eta)dd(x)
  . $ Take $eta$ to be a decreasing sequence $eta_k$ that converges pointwise
  to $Id_(B(0,r))$ and such that $
    lim_(k->oo)int_E abs(nd eta_k)=dv(,r)cal(H)^(n+1)(E sect B(0,r))
  . $ Hence $
    int_(B(0,r))nu_(n+1)dd(mu_E)<=dv(,r)cal(H)^(n+1)(E sect B(0,r))
  $ for a.e. $r in (0,r_0)$. Hence there is $r_1$ such that for a.e.
  $r in (0,r_1)$, $
    mu_E (B(0,r))<=2dv(,r)cal(H)^(n+1)(E sect B(0,r))=
    2cal(H)^n (E sect pt B(0,r))<=2(n+1)omega_(n+1)r^n
  . $ (Notice that since LHS is monotone and RHS is continuous, we may remove
  a.e. in the statement). Then by the compact theorem of BV functions, we can
  select a sequence
  $r_k->0$ such that $
    Id_(r_k^(-1) E)-->Id_F "in" L_"loc"^1 (RR^(n+1))
  , $ where $F$ is a set of locally finite perimeter in $RR^(n+1)$. Hence for
  any non-negative $eta in C_0^1$, $
    lim_(k->oo)int_(r_k^(-1) E)nd_i eta dd(x)=int_F nd_i eta dd(x)
  . $ Now let $eta_k (x)=eta(r_k^(-1)x)$, we see $
    int_(r_k^(-1)E)nd_i eta dd(x)=r_k^(-n)int_E nd_i eta_k dd(x)=
    -r_k^(-n)int_U eta_k nu_i dd(mu_E)
  . $ Let $k->oo$ we have $
    int_F nd_i eta dd(x)=0,quad forall eta in C_0^1\(RR^(n+1)),1<=i<=n
  . $ It follows that $F=RR^(n)times H$ for some Lebesgue measurable $H cc RR$.
  On the other hand, take $X=eta_k e_(n+1)$, we have for large $k$, $
    0>=-r_k^(-n)int_U eta_k nu_(n+1)dd(mu_E)&=int_(r_k^(-1)E)nd_(n+1)eta dd(x) \
    &->int_F nd_(n+1)eta=int_(RR^n)int_H pdv(eta,x^(n+1)) dd(x^(n+1))dd(x') \
    &=pari(pt_(n+1)Id_H,eta) quad "(for every" eta "non-negative)"
  . $ Hence $Id_H$ is non-increasing in the distribution sense, #ie $H$ is
  a.e. $(-oo,lambda)$ for some $lambda in RR$. Then $F={x^(n+1)<lambda}$.

  Next we want to show this $c$ is actually 0. Apply Sobolev inequality $
    norm(u)_(L^(1+1/n))<=C norm(nd u)_(L^1), u in W_0^(1,1) "(or" BV_"loc""?)"
  $ to $u=eta dot.c (chi_eps * Id_E)$. Where $spt eta cc U_eps$ and $chi_eps$ is
  the favorite kernel. We get $
    norm(eta dot.c (chi_eps * Id_E))_(L^(1+1/n)(U))
    &<=C norm(nd (eta dot.c (chi_eps * Id_E)))_(L^1) \
    &<=C(int_U eta abs(nd(chi_eps*Id_E))dd(x)
      +int_U abs(nd eta)(chi_eps*Id_E)dd(x))
  . $ Let $eps->0$ we get $
    (int_E eta^((n+1)/n)dd(x))^(n/(n+1))<=C(int_U eta dd(mu_E)
    +int_E abs(nd eta)dd(x))
  . $ Replace $eta$ by $eta_k$ we see for small $r$, $
    cal(H)^(n+1)(E sect B(0,r))^(n/(n+1))
    &<=C(mu_E (B(0,r))+dv(,r)cal(H)^(n+1)(E sect B(0,r))) \
    &<=C_1 dv(,r)cal(H)^(n+1)(E sect B(0,r))quad "(previous estimate)"
  . $ Hence $
    dv(,r)cal(H)^(n+1)(E sect B(0,r))^(1/(n+1))>=C_2>0 "for a.e." r<r_1
  . $ Integrate we get $
    cal(H)^(n+1)(E sect B(0,r))>=C r^(n+1) "for small" r
  . $ Repeat the same argument for $U\\E$ we have $
    cal(H)^(n+1)(sect B(0,r)\\E)>=C r^(n+1)
  . $ This forces that $lambda=0$.

  We conclude that $
    Id_(r_k^(-1)E)xarrow(L_"loc"^1)Id_({x^(n+1)<0}) "as" k->oo
  . $ Easy to use subsubsequence argument to get $
    Id_(r^(-1)E)xarrow(L_"loc"^1)Id_({x^(n+1)<0}) "as" r->0
  . $ Hence $
    mu_(r^(-1)E)-->mu_({x^(n+1)<0})=lr(cal(H)^n|)_({x^(n+1)=0}) "as" r->0
  . $ Similar thing holds around every $x in pt^*E$. In particular, $
    (mu_E (B(x,r)))/(omega_n r^n)->1, forall x in pt^*E
  . $ By the comparison theorem, we have $
    lr(cal(H)^(n)|)_(pt^*E)<=mu_E "in" U
  . $ In particular $lr(cal(H)^n|)_(pt^*E)$ is absolutely continuous with
  respect to $mu_E$, and $pt^*E$ is $cal(H)^n$-measurable with locally finite
  $cal(H)^n$-measure. We can repeat the argument as in @rect-criterion,
  replace $mu$ by $mu_E$, to see that $pt^*E$ is $n$-rectifiable.

  Next, let $A cc pt^*E$, $
    A_k={x in A:mu_E (B(x,r))<=2omega_n r^n, forall r<1/k}
  . $ Then $A=union_k A_k$. By definition of Hausdorff measure, we can choose
  $C_(k j)$ such that $A_k cc union_j C_(k j)$, $C_(k j)sect A_k!=OO$,
  $op("diam")C_(k j)<1/k$, and $
    sum_j omega_n (1/2 op("diam")C_(k j))^n<=cal(H)^n_(1\/k) (A_k)+1/k
  . $ Then, let $x_(k j) in A_k sect C_(k j)$, and $r_(j k)=op("diam")C_(k j)$,
  we have $
    mu_E (A_i)<=sum_j mu_E (B(x_(j k),r_(j k)))<=2^(n+1)(cal(H)^n_(1\/k)(A)+1/k)
  . $ Let $k->oo$, we see $mu_E <=2^(n+1)lr(cal(H)^n|)_(pt^*E)$ in $U$. So
  $mu_E$ is also absolutely continuous w.r.t. $lr(cal(H)^n|)_(pt^*E)$.

  Write $pt^*E=M_0union union_(i>0)M_i$, where $M_0$ is $cal(H)^n$-null and
  $M_i cc N_i$ $n$-dim embedded $C^1$-submanifold. Then by upper density theorem
  we have $
    (mu_E (B(x,r)))/(cal(H)^n (N_j sect B(x,r)))->1,
    "for" cal(H)^n"-a.e." x in M_j
  . $ Then Radon-Nikodym theorem shows that $mu_E=lr(cal(H)^n|)_(pt^*E)$.
]

#example[
  As an application, we may fix a bounded (smooth) region, say a ball, and
  consider all the sets with locally finite perimeter that differs from a big
  region cutting the ball, say a half space, only outside the ball. Then taking
  minimizing sequence (minimizing the local perimeter) of such sets will give a
  set of locally finite perimeter with boundary a minimal surface.
]

== Integral varifolds
#definition[
  Let $U cc RR^(n+k)$ open, a _rectifiable_ $n$-_varifold_ is a pair
  $V=(M,theta)$, where $M cc U$ is $n$-rectifiable and $theta$ is a positive,
  locally integrable $cal(H)^n$-measurable function on $M$, called the
  _multiplicity function_. Two varifolds are the same if $M$ only differ in a
  $cal(H)^n$-null set and $theta$ is agrees $cal(H)^n$-a.e. If $theta$ is
  integer valued, $V$ is called _integral_.

  There is a Radon measure on $U$ defined by $
    mu_V (A)=int_(A sect M)theta dH(n)
  , $ called the _weight measure_ of $V$. The total mass of $V$ is defined by $
    Vol(V)=mu_V (U)=int_M theta dH(n)
  . $ And $
    spt mu_V:={x in U:mu_V (B(x,r))>0, forall r>0}
  . $ 
]

Suppose there is an injective Lipschitz $f:spt mu_V->W cc RR^(n+l)$. Then we can
define $
  f_* V=(f(M),tilde(theta)),quad tilde(theta)=theta compose f^(-1)
. $ Note that the area formula gives $
  int_(f(M)sect K)tilde(theta)dH(n)
  =int_(M sect f^(-1)(K))theta cal(J)_f^M dH(n)
. $ Note that $f^(-1)(K)$ may be unbounded for general $f$. So we need to assume
that $f$ is proper, #ie $f^(-1)(K)$ is compact for compact $K$. We may remove
the assumption that $f$ is injective, then we define $tilde(theta)$ by $
  tilde(theta)(y)=sum_(x in f^(-1)(y)sect M)=int_(f^(-1)(y)sect M)theta dH(0)
. $ It is locally integrable by the area formula: $
  int_(f(M)sect K)tilde(theta)dH(n)=int_(M sect f^(-1)(K))theta cal(J)^M_f dH(n)
. $ 

#definition[
  Let $V$ be a rectifiable $n$-varifold in $U cc RR^(n+k)$. We say a $n$-dim
  affine subspace $W$ through $p$ is the approximate tangent space of $V$ at
  $x$ if for any $f in C_0^0$, $
    lim_(eps->0)int_(1/eps (M-x)+x)f(y)theta(x+eps y)dH(n)(y)
    =theta(x)int_W f(y)dH(n)(y)
  . $ 
]
#theorem[
  Suppose $V=(M,theta)$ is a rectifiable $n$-varifold in $U cc RR^(n+k)$, then
  $V$ has an approximate tangent space $T_x V$ for $cal(H)^n$-a.e. $x in M$.
]
#remark[
  In particular, $x$ is a density point of $theta$, whenever $T_x M$ exists.
]

== First variation & Monotonicity formula
We consider only the _ambient variations_ of a varifold, that is, a $C^1$
$vphi:(-eps,eps)times U->RR^(n+k)$, supported on a compact set and $vphi(0,x)=x$
for all $x in U$. Area formula gives $
  Vol (vphi_(t*)(V angle.right K))=int_(M sect K)cal(J)_(vphi_t)^M dd(mu_V)
. $ The first variation is given exactly by $
  lr(dv(,t)|)_(t=0)Vol(V_t)=int_M div_M X dd(mu_V)
. $ Here $div_M$ is $mu_V$-a.e. defined as long as the tangent space exists.
$V$ is called stationary if the first variation is 0 for any $vphi_t$, #ie $
  int_M div_M X dd(mu_V)=0, forall X in C_0^1 (U,RR^(n+k))
. $ We call the distribution $-div_M dd(mu_V)$ the mean curvature of $V$, roughly
denoted by $H dd(mu_V)$. Note that the mean curvature can be decomposed into $
  -div_M dd(mu_V)=H_n dd(mu_V)+dd(nu_V)
. $ Here $H_n$ is the mean curvature of $N_j$ on $M_j cc N_j$, which is a well
defined $L^1_"loc"$ function, and $dd(nu_V)$ is the boundary measure from
divergence theorem on $V$, which may be very singular. Note $H$ has the same
support as $mu_V$ as a distribution.

For a varifold $V$ stationary in $U$, let $eta(r)$ be smooth monotone decreasing,
supported on $(-oo,R)$ and is 1 on $(-oo,rho]$. WLOG $0 in U$ and $B(0,R)cc U$.
Let $r=abs(x)$, $X=eta(r)x=r eta(r)nd r^sharp$, then  $
  0&=int_M div_M X dd(mu_V)=int_M sum_i e_i dot.c nd_(e_i)X dd(mu_V)\
  &=int_M sum_i eta'(r)(abs(e_i dot.c x)^2)/r+eta(r)e_i dot.c e_i dd(mu_V) \
  &=int_M n eta(r)+r eta'(r)abs(x^breb/r)^2 dd(mu_V) \
  &=n int_M eta(r)dd(mu_V)+int_M r eta'(r)abs(nd^M r)^2 dd(mu_V)
. $ (Here $nd$ is the (flat) connection on $RR^(n+k)$, $nd_v r=(v dot.c x)/r$,
$nd_v x=v$). More generally we may consider $X=eta(r)h(x)(x-y)$, for now let
$h==1$. Take $eta(r)=vphi(r\/rho)$, where $vphi(t)==1$ for $t<=1$ and
$vphi(t)=0$ for $t>=1+eps$. Then we have $
  n int_M vphi(r\/rho)dd(mu_V)-rho dv(,rho)int_M abs(nd^M r)^2 vphi(r\/rho)
  dd(mu_V)=0
. $ Let $I(rho)=int_M vphi(r\/rho)dd(mu_V)$, since $abs(nd^M r)^2+abs(nd^perp
r)^2=1$, we have $
  n I(rho)-rho I'(rho)=int_M (r\/rho)vphi'(r\/rho)abs(nd^perp r)^2 dd(mu_V)
. $ So $
  dv(,rho)(rho^(-n)I(rho))=int_M rho^(-n)dv(,rho)(vphi(r\/rho))abs(nd^perp r)^2
  dd(mu_V)
. $ Since $vphi'(r\/rho)$ nonzero only for $r in[rho,(1+eps)rho]$, we have $
  r^(-n)dv(,rho)(vphi(r\/rho))<=rho^(-n)dv(,rho)(vphi(r\/rho))
  <=(1+eps)^n r^(-n)dv(,rho)(vphi(r\/rho))
. $ Hence $
J'(rho)<=dv(,rho)(rho^(-n)I(rho))<=(1+eps)^n J'(rho),quad
J(rho)=int_M r^(-n) abs(nd^perp r)^2 vphi(r\/rho)dd(mu_V)
. $ Integrate on interval $[r_1,r_2]$ and let $eps->0$, we get $
  (mu_V B(0,r_2))/(omega_n r_2^n)-(mu_V B(0,r_1))/(omega_n r_1^n)
  =omega_n^(-1) int_(B(0,r_2)\\B(0,r_1)) abs(nd^perp r)^2/r^n dd(mu_V)
$ for all $0<r_1<=r_2<R$ and $B(x,R)cc U$. Hence the density $Theta^n (mu_V,x)$
of $mu_V$ w.r.t. $cal(H)^n$ exists for every $x in U$ and is upper
semi-continuous. Also this shows that $
  int_(B(x,eps)) abs(nd^perp abs(y-x))^2/abs(y-x)^n dd(mu_V)(y)<oo,quad
  forall B(x,eps)cc U
. $ Note that $Theta^n (mu_V,x)=theta(x)$ $cal(H)^n$-a.e. So we can choose
canonical representatives $M_V,Theta_V$ for $V$, by $
  Theta_V (x)=Theta^n (mu_V,x),quad M_V={x in U:Theta_V (x)>0}
. $ Since $Theta_V$ is upper semi-continuous, the set ${Theta_V>=c}$ is closed
in $U$ for any $c>0$. 

- #text(blue)[Will $Theta_V$ be integer valued if $theta$ is?]
- #text(red)[No, center of a Y shape will have $Theta_V=3/2$.]
- #text(blue)[What's the point of $U$?]
- #text(red)[A disk is not minimal itself, but is minimal in a ball.]

We can generalize the monotonicity formula with certain bound on mean curvature.
Choose $X=h(x)eta(r)(x-y)$ we have $
  int (n eta(r)+r eta'(r)lr(|nd^M r|,size:#80%)^2)h dd(mu_V)
  =-int (x-y) dot.c (h H+nd^M h)eta(r)dd(mu_V)
. $ Now suppose $B(y,R)cc U$ and $norm(H)_(L^oo)<=R^(-1)Lambda$. Let $h=1$,
repeat the above calculation we get $
  J'(rho)<=dv(,rho)(rho^(-n)I(rho))+E_1 (rho)<=(1+eps)^n J'(rho)
, $ where $
  E_1 (rho)=rho^(-n)int (r\/rho)vphi(r\/rho)nd r dot.c H dd(mu_V)
. $ Since $vphi(t)$ is 0 when $t>=1+eps$, we can estimate $
  abs(E_1 (rho))<=(1+eps)rho^(-n)int vphi(r\/rho) abs(H)dd(mu_V)
  <=(1+eps)Lambda R^(-1)rho^(-n)I(rho)
. $ So $E_1 (rho)=alpha(rho)rho^(-n)I(rho)$, where $|alpha(rho)|
<=(1+eps)Lambda\/R$.
Let $
  F(rho)=int_0^rho alpha(t)dd(t),quad abs(dot.c)<=(1+eps)Lambda rho\/R
  <=(1+eps)Lambda
, $ we obtain $
  e^(-(1+eps)Lambda)J'(rho)<=dv(,rho)(e^(F(rho))rho^(-n)I(rho))
  <=e^((1+eps)Lambda)J'(rho)
. $ Again integrate over $[r_1,r_2]$ we see for all $0<r_1<=r_2<R$, $
  e^(F(r_2))(mu_V B(0,r_2))/(omega_n r_2^n)
  -e^(F(r_1))(mu_V B(0,r_1))/(omega_n r_1^n)
  =G(r_1,r_2)/omega_n int_(B(0,r_2)\\B(0,r_1)) abs(nd^perp r)^2/r^n dd(mu_V)
, $ where $G(r_1,r_2)in \[e^(-Lambda),e^(Lambda)]$.

Since $abs(F(rho))<=Lambda rho\/R$, this also implies the existence of
$Theta^n(mu_V,x)$ for any $x in U$.

- #text(purple)[Skipped some discussion here.]

If $H$ is merely $L^p$ rather than $L^oo$, let's come back to estimate $
  E_1 (rho)=rho^(-n)int (r\/rho)vphi(r\/rho)nd r dot.c H dd(mu_V)
. $ Assume $p>n$ and $
  R^(1-n/p)norm(H)_(L^p (mu_V angle.right B(0,R)))<=Lambda
. $ Then by Hölder inequality, $
  abs(E_1 (rho))&<=(1+eps)rho^(-n)norm(H)_(L^p (mu_V angle.right B(0,R)))
  (I(rho))^(1-1/p) \
  &=(1+eps)Lambda R^(-1)(rho\/R)^(-n/p) (rho^(-n)I(rho))^(1-1/p) \
  &<=(1+eps)Lambda R^(-1)(rho\/R)^(-n/p)(1/p+rho^(-n)I(rho))
. $ The last inequality use the fact that $a^(1-1/p)<=1/p+(1-1/p)a<=1/p+a$
for any $a>=0$. Then we have $
  J'(rho)<=dv(,rho)(rho^(-n)I(rho))+alpha_p (rho)(1/p+rho^(-n)I(rho))
  <=(1+eps)^n J'(rho)
, $ where $
  abs(alpha_p (rho))<=(1+eps)Lambda R^(-1) (rho\/R)^(-n/p)
. $ Again let $F(rho)=int_0^rho alpha(t)dd(t)$, then $
  abs(F(rho))<=(1+eps)(Lambda p)/(p-n)(rho\/R)^(1-n/p)<=(1+eps)(Lambda p)/(p-n)
. $ Then $
  e^(-(1+eps)(Lambda p)/(p-n))J'(rho)
  <=dv(,rho)(e^(F(rho))rho^(-n)I(rho)+1/p e^(F(rho)))
  <=(1+eps)^n e^((1+eps)(Lambda p)/(p-n)) J'(rho)
. $ Finally we get for $0<r_1<=r_2<R$, $
  &(e^(F(r_2))(mu_V B(0,r_2))/(omega_n r_2^n)+1/(p omega_n) (e^(F(r_2))-1))
  -(e^(F(r_1))(mu_V B(0,r_1))/(omega_n r_1^n)+1/(p omega_n) (e^(F(r_1))-1)) \
  &=G(r_1,r_2)/omega_n int_(B(0,r_2)\\B(0,r_1)) abs(nd^perp r)^2/r^n dd(mu_V),
  quad quad G(r_1,r_2)in lr([e^(-(Lambda p)/(p-n)),e^((Lambda p)/(p-n))],
  size:#70%)
. $ Again we have $
  e^(F(r))(mu_V B(x,r))/(omega_n r^n)+1/(p omega_n) (e^(F(r))-1)
  -->Theta^n (mu_V,x),quad "as" r->0, forall x in U
, $ and the density is upper semi-continuous in $U$.

#remark[
- If $H$ is $L^p_"loc" (mu_V)$, $p>n$ and if $theta>=1$ $mu_V$-a.e. Then by
  the upper semi-continuity, $Theta^n (mu_V,x)>=1$ everywhere on $spt mu_V$.
  In this case the canonical representative $M_V$ will be the closed subset
  $spt mu_V$.
- If $r^(-n)mu_V (B(x,r))<=C_0$, then we have bound $
    mu_V (B(x,r))<=beta r^n, quad forall r<R, beta=beta(Lambda,C_0)
  . $ It follows that for any $0<r_1<=r_2<R$, $
  int_(B(x,r_2)\\B(x,r_1))dd(mu_V)/abs(y-x)^q<=n beta (r_2^(n-q)-r_1^(n-q))/(n-q)
  (=beta log (r_2\/r_1) "when" q=n)
  . $ 
]

== Local conical approximation
In this section we assume $V=(M,theta)$ is a varifold with locally $L^p$ mean curvature, $p>n$.
#theorem(name: "Conical Approximation")[
  Suppose $Lambda>0$, $0<lambda<=1/4$, $0<=delta<=1/16$, and
  - $0 in spt mu_V$, $Theta^n (mu_V,0)<=Lambda$, #h(1fr)
  - $omega_n^(-1)mu_V (B(0,1)))<=Theta^n (mu_V,0)+delta$,
  - $norm(H)_(L^p (B(0,1))<=delta$.
  Then $
    (mu_V B(x,\(1-delta^(1/4)\)r))/(omega_n r^n)-C kappa(delta,lambda)<=
    (mu_V B(t x,t r))/(omega_n (t r)^n)<=
    (mu_V B(x,\(1+delta^(1/4)\)r))/(omega_n r^n)+C kappa(delta,lambda)
  $ for all $x in B(0,1)\\B(0,2lambda)$, $lambda<=t<=1$ and all $r$ with $
    lambda<=r<=min lr({abs(x)-lambda,(1-abs(y))/(1+delta^(1/4))},size:#50%)
  , $ where $C=C(n,p,Lambda)$ and $
    kappa(delta,lambda)=lambda^(-n)delta+delta^(1/4)abs(log lambda)
  . $ 
]
#remark[
  - When $H=0$ and $omega_n^(-1)mu_V (B(0,1))=Theta^n (mu_V,0)$, we can apply the theorem with $delta=0$ and
    $lambda$ arbitrarily small. We conclude that $Theta^n (mu_V,t x)=Theta^n (mu_V,x)$ for any $0<t<=1$ Hence
    $V angle.right B(0,1)$ is a cone.
  - For $x_0 in spt V$, consider $V_eps=1/eps (V-x_0)$. The $L^p$-norm of $H$ in $B(0,1)$ converges to 0 as
    $eps->0$. We can apply the theorem with arbitrarily small $delta$ by taking $eps$ small enough. \
    If $Theta^n (mu_V,x)>=1$ on $spt mu_V$, the Allard compactness theorem guarantees that there is a
    subsequence $mu_(V_eps)->mu_W$ for some $n$-varifold $W$, which is stationary in $RR^(n+k)$ and has
    multiplicity $>=1$ on $spt mu_W$. $W$ is a cone by above theorem, called a tangent cone of $V$ at $x$.
    It is still open to ask whether $W$ is unique.
]
#proof[
  First assume $delta>0$. By the monotonicity formula we have $
    int_(B(0,1))abs(nd^perp r)^2/r^n dd(mu_V)<=C delta, quad C=C(n,p,Lambda)
  . $ 
]

== Poincaré and Sobolev inequalities
In this section we assume $V=(M,theta)$ has $H in L_"loc"^p$ and $theta>=1$ $mu_V$-a.e. So $Theta^n (mu,x)>=1$
everywhere on $spt mu sect U$. For simplicity, we write $mu=mu_V$, and all integrals are over $M$ if not
specified. Recall that we have $
  pdv(,rho)(rho^(-n)I(rho))=&rho^(-n)pdv(,rho)int abs(nd^perp r)^2 h vphi(r\/rho)dd(mu) \
  &+rho^(-n-1)int (x-x_0)dot.c (nd^M h+H h)vphi(r\/rho)dd(mu) \
  text(#blue,("for" h>=0))>=&rho^(-n-1)int (x-x_0)dot.c (nd^M h+H h)vphi(r\/rho)dd(mu)
, $ where $I(rho)=int vphi(r\/rho) h dd(mu)$, $vphi$ is $1$ on $(-oo,1]$ and supported on $(-oo,1+eps]$.
We can estimate RHS in two ways:
- If $norm(H)_(L^oo)<=Lambda$, we have #h(1fr) $
    "RHS">=-(Lambda rho)rho^(-n)I(rho)-rho^(-n-1)int r abs(nd^M h)vphi(r\/rho)dd(mu)
  . $ 
- For arbitrary $H$, we have $
    "RHS">=-rho^(-n-1)int r(abs(nd^M h)+h abs(H))vphi(r\/rho)dd(mu)
  . $ 
Integrate and let $eps->0$, we get
- Using 2nd estimate, $
    1/(omega_n r^n)int_(B(x_0,r))h dd(mu)&<=1/(omega_n R^n) int_(B(x_0,R))h dd(mu)
    +1/(omega_n)int_r^R 1/t^(n+1) int_(B(x_0,t))(abs(nd^M h)+h abs(H))r dd(mu)dd(t) \
    &<=1/(omega_n R^n) int_(B(x_0,R))h dd(mu)
    +1/(n omega_n)int_(B(x_0,R))(abs(nd^M h)+h abs(H))/abs(x-x_0)^(n-1)dd(mu)
  . $ 
- Using 1st estimate, #h(1fr) $
    e^(Lambda r)/(omega_n r^n)int_(B(x_0,r))h dd(mu)<=&e^(Lambda R)/(omega_n R^n) int_(B(x_0,R))h dd(mu)
    +e^(Lambda R)/(n omega_n)int_(B(x_0,R))abs(nd^M h)/(abs(x-x_0)^(n-1))dd(mu)
  , $ where $B(x_0,R)cc U$ and $0<r<R$.
In particular, let $r->0$, since $Theta^n (mu,x_0)>=1$, we get $
    h(x_0)<=&e^(Lambda R)/(omega_n R^n) int_(B(x_0,R))h dd(mu)
    +e^(Lambda R)/(n omega_n)int_(B(x_0,R))abs(nd^M h)/(abs(x-x_0)^(n-1))dd(mu)
. $ 
#theorem(name:"Poincaré type inequality")[\
  Suppose $h in C^1 (U)$ non-negative, $B(x_0,2R)cc U$, $abs(H)<=Lambda$, $theta>=1$ $mu$-a.e. and there are
  $0<alpha<1$ and $Gamma>0$ #st $
    mu({h(x)>0}sect B(x,R))<=(1-alpha)omega_n R^n,quad e^(Lambda R)<=1+alpha,quad mu(B(x,2R))<=Gamma R^n
  . $ Then there are $beta=beta(n,alpha,Gamma)in lr((0,1/2),size:#80%)$ and $C=C(n,alpha,Gamma)>0$ #st $
    int_(B(x_0,beta R))h dd(mu)<=C R int_(B(x_0,R))abs(nd^M h)dd(mu)
  . $
]
#proof[
  First we take an arbitrary $beta in lr((0,1/2),size:#80%)$, apply above inequality we get $
    h(y)&<=e^(Lambda(1-beta)R)/(omega_n ((1-beta)R)^n)int_(B(y,(1-beta)R))h dd(mu)
    +e^(Lambda(1-beta)R)/(n omega_n)int_(B(y,(1-beta)R))abs(nd^M h)/(abs(x-y)^(n-1))dd(mu) \
    &<=e^(Lambda(1-beta)R)/(omega_n ((1-beta)R)^n)int_(B(x_0,R))h dd(mu)
    +e^(Lambda(1-beta)R)/(n omega_n)int_(B(x_0,R))abs(nd^M h)/(abs(x-y)^(n-1))dd(mu)
  . $ Let $eta:RR->[0,1]$ smooth non-decreasing that is supported on $[0,oo]$. Apply above with $h$ replaced
  by $eta(h-t)$, $t>=0$, we get $
    eta(h(y)-t)<= (1-alpha^2)/(1-beta)^n
    +(1+alpha)/(n omega_n)int_(B(x,R))(eta'(h-t)abs(nd^M h))/(x-y)^(n-1)dd(mu)
  . $ Choose small $beta$ such that $
    (1-alpha^2)/(1-beta)^(-n)<=1-alpha^2/2
  , $ then for any $y in B(x_0,beta R)sect spt mu$ such that $eta(h(y)-t)>=1$, $
    alpha^2/2<= (1+alpha)/(n omega_n)int_(B(x_0,R))(eta'(h-t)abs(nd^M h))/(x-y)^(n-1)dd(mu)
  . $ Now let $eps>0$ and let $eta==1$ on $[1+eps,oo)$. Then we have  $
    1<=C int_(B(x_0,R))(eta'(h-t)abs(nd^M h))/(x-y)^(n-1)dd(mu),quad y in B(x_0,beta R)sect A_(t+eps)
  , $ where $A_s={h(y)>s}sect spt mu$. Integrate both side over $A_(t+eps)sect B(x_0,beta R)$ we get $
    mu(A_(t+eps)sect B(x_0,beta R))&<=C int_(B(x_0,R))eta'(h(x)-t)abs(nd^M h(x))int_(B(x_0,beta R))
    1/abs(x-y)^(n-1)dd(mu)\(y\)dd(mu)(x) \
    &<=C Gamma R int_(B(x_0,R))eta'(h-t)abs(nd^M h)dd(mu)
  . $ Note that $
    eta'(h(x)-t)=-dv(,t)(eta(h(x)-t))
  , $ integrate w.r.t $t in (0,oo)$ we get $
    int_(A_eps sect B(x_0,beta R))h-eps dd(mu)<=C Gamma R int_(B(x_0,R))abs(nd^M h)dd(mu)
  . $ Let $eps->0$ we get the desired inequality.
]
#remark[
  If we drop the assumption $theta>=1$, we still have $
    int_({theta>=1}sect B(x_0,beta R))h dd(mu)<=C R int_(B(x_0,R))abs(nd^M h)dd(mu)
  . $ 
]
#lemma[
  Suppose $f,g:RR->RR_(>0)$ are increasing and bounded, and $
    1<=r^(-n) f(r)<=R^(-n)f(R)+int_0^R t^(-n)g(t)dd(t),quad forall 0<r<R<oo
  . $ Then there exists $R$ with $0<R<R_0=2f(oo)^(1/n)$ such that $
    f(5R)<= (5^n R_0 g(R))/2
  . $ 
]
#proof[
  Suppose not true for any $R in (0,R_0)$. Then $
    sup_(0<r<R_0)r^(-n)f(r)&<=R_0^(-n)f(R_0)+int_0^(R_0)r^(-n)g(r)dd(r) \
    &<=R_0^(-n)f(R_0)+2/(5^n R_0)int_0^(R_0)r^(-n)f(5r)dd(r) \
    &=R_0^(-n)f(R_0)+2/(5 R_0)int_0^(5R_0)r^(-n)f(r)dd(r) \
    &=R_0^(-n)f(R_0)+2/(5 R_0)(int_0^(R_0)r^(-n)f(r)dd(r)+int_(R_0)^(5R_0)r^(-n)f(r)dd(r)) \
    &<=R_0^(-n)f(oo)+2/5 sup_(0<r<R_0) r^(-n)f(r)+2/(5(n-1))R_0^(-n)f(oo)
  . $ So $
    3<=3sup_(0<r<R_0)r^(-n)f(r)<=lr((5+2/(n-1)),size:#70%)R_0^(-n)f(oo)=2^(-n)lr((5+2/(n-1)),size:#70%)
  , $ which is impossible when $n>=2$.
]
#theorem(name:"Sobolev inequality")[\
  Suppose $h in C_0^1 (U)$ non-negative, $theta>=1$ $mu$-a.e. Then there is $C=C(n)$ #st $
    (int h^(n/(n-1))dd(mu))^((n-1)/n)<=C int abs(nd^M h)+h abs(H)dd(mu)
  . $
]
#proof[
  Recall that $
    1/(omega_n r^n)int_(B(x_0,r))h dd(mu)<=1/(omega_n R^n) int_(B(x_0,R))h dd(mu)
    +1/(n omega_n)int_(B(x_0,R))(abs(nd^M h)+h abs(H))/abs(x-x_0)^(n-1)dd(mu)
  . $ Since $h$ is compactly supported in $U$, this holds for any $0<r<R<oo$. Apply lemma with $
    f(r)&=1/omega_n int_(B(x_0,r))h dd(mu) \
    g(r)&=1/omega_n int_(B(x_0,r))abs(nd^M h)+h abs(H) dd(mu)
  , $ where $x_0 in spt mu$, $h(x_0)>=1$. There exists $r_0<2(omega_n^(-1)int_M h dd(mu))^(1/n)$
  such that $
    int_(B(x_0,5r_0))h dd(mu)<=5^n lr((omega^(-1) int_M h dd(mu)),size:#70%)^(1/n)
    int_(B(x_0,r_0))abs(nd^M h)+h abs(H)dd(mu)
  . $ Using the covering lemma we can select disjoint balls $B(x_i,r_i)$ where $x_i in {h>=1} sect spt mu$
  such that ${h>=1}sect spt mu cc union_i B(x_i,5r_i)$. So $
    int_({h>=1}sect spt mu)h dd(mu)<=5^n lr((omega^(-1) int_M h dd(mu)),size:#70%)^(1/n)
    int_(M)abs(nd^M h)+h abs(H)dd(mu)
  . $ Now choose $eta$ non-decreasing that is $1$ on $(eps,oo)$ and supported on $[0,oo)$, replace $h$ by
  $eta(h-t)$, $t>=0$. We get $
    mu(M_(t+eps))<=5^n (omega_n^(-1)mu(M_t))^(1/n)int_M eta'(h-t)abs(nd^M h)+eta(h-t)abs(H)dd(mu)
  , $ where $M_s={h>s}sect M$. Hence $
    (t+eps)^(1/(n-1))mu(M_(t+eps))&<=5^n (omega_n^(-1)(t+eps)^(n/(n-1))mu(M_t))^(1/n)int_M
    eta'(h-t)abs(nd^M h)+eta(h-t)abs(H)dd(mu) \
    &<=5^n omega_n^(-1/n)lr((int_M (h+eps)^(n/(n-1))dd(mu)),size:#16pt)^(1/n)
    lr((-dv(,t)int_M eta(h-t)abs(nd^M h)dd(mu)+int_(M_t)abs(H)dd(mu)),size:#16pt)
  . $ Integrate for $t in (0,oo)$ gives $
    int_(M_eps)h^(n/(n-1))-eps^(n/(n-1))dd(mu)
    <=5^n omega_n^(-1/n)lr((int_M (h+eps)^(n/(n-1))dd(mu)),size:#16pt)^(1/n)
    int_M abs(nd^M h)dd(mu)+h abs(H)dd(mu)
  . $ Let $eps->0$, we obtain the desired inequality.
]
#remark[
  The inequality remains valid as long as $H$ is locally integrable.
]
- #text(blue)[What if no $h>=0$?]
- #text(red)[Split $h$ into $h_+$ and $h_-$ and everything works.]

#theorem(name:"Convex hull property for minimal surfaces")[
  Suppose $K cc RR^(n+k)$ is compact, $U=RR^(n+k)\\K$, $V=(M,theta)$ is stationary in $U$ and $mu_V$ has
  compact support, then $
    spt mu_V cc "convex hull of" K
  . $ 
]
#let ov = math.overline
#proof[
  Only need to prove for $K$ be a closed ball, for general $K$, then the theorem follows by $
    "convex hull of" K=sect.big_(K cc overline(B)(x,R))#h(-5pt) overline(B)(x,R)
  . $ Now suppose $K=ov(B)(x_0,R)$. Recall the identity ($r=abs(x-x_0)$): $
    n int_U eta(r)dd(mu_V)+int_U r eta'(r)(abs(nd^M r)^2)dd(mu_V)=-int_U eta(r)(x-x_0)dot.c H dd(mu_V)=0
  . $ When $mu_V$ has compact support, the identity holds for any non-negative non-decreasing $eta$ supported
  on $[R+eps,oo)$. Since $eta>=0$, we can choose $eta==1$ on $[R+2eps,oo)$, then we must have  $
    mu_V (B^c (x_0,R+2eps))=0
  . $ Hence $mu_V$ is supported on $ov(B)(x_0,R+2eps)$. Since $eps$ is arbitrary, we conclude that $mu_V$
  supported on $ov(B)(x_0,R)$.
]
#remark[
  The ball version is still true if we only assume $H dot.c (x-x_0)>-n$ for $mu_V$-a.e.
]
#definition[
  The _Hausdorff distance_ of two precompact set $A,B$ in a metric space is defined as $
    d_"H" (A,B)=inf{eps:A cc B_eps "and" B cc A_eps},quad
    A_eps:={x:d(x,A)<eps}
  . $ 
]
#theorem(name:"Hausdorff compactness")[
  Let $p>n$ and ${V_i}={M_i,theta_i}$ be varifolds in $U$ with $H_(V_i) in L^p_"loc"
  lr((mu_(V_i),U),size:#10pt)$, $Theta^n lr((mu_(V_i),x),size:#10pt)>=1$ for all $x in spt mu_(V_i)$ and
  $mu_(V_i)$, $lr(norm(H_(V_i)),size:#12pt)_(L^p)$ are locally uniformly bounded, #ie uniformly bounded in
  $i$ on every compact $K$. Then there is subsequence that $mu_(V_i)$ converges weakly to a Radon measure
  $mu$ and $spt mu_(V_i)$ converges locally under Hausdorff distance to $spt mu$.
]
#proof[
  The space of signed Radon measures is the Banach dual of the space of compactly supported continuous
  functions. So bounded sequence has a weakly convergent sequence. Denote by $
    M_i^eps={x in U:d lr((x,spt mu),size:#12pt)<eps}
  . $ Fix a compact $K$ and $eps>0$. For $x in U$, if there are infinitely many $i$ such that $x in.not
  M_i^eps$, pick continuous function $vphi$ that is non-negative, supported on $B(x,eps\/2)$, and $vphi==1$ on
  $B(x,eps\/4)$, we see $
    int_U vphi dd(mu)=lim_(i->oo) int_U vphi dd(mu_(V_i))=0
  . $ So $B(x,eps\/4) sect spt mu=OO$. Hence $
    K sect spt mu cc union.big_(N>=0) sect.big_(i>=N)M_i^eps
  . $ Since $K$ is compact and $spt mu$ is closed, there is an $N$ such that $
    K sect spt mu cc sect.big_(i>=N)M_i^eps
  . $ Now suppose there is a subsequence that $forall i$, $
    K sect spt mu_(V_i) cc.not A_eps:={x in U:d lr((x,spt mu),size:#12pt)<eps}
  . $ Let $x_i in K sect mu_(V_i)$ such that $x_i in.not A_eps$. Since $K$ is compact, by passing to
  subsequence we may assume $x_i->x_oo in K$ and $x_oo in.not A_eps$. Then by the convergence, $
    limsup_(i) mu_(V_i) (B(x_oo,eps\/3))<=mu(B(x_oo,eps\/2))=0
  . $ However, $B(x_i,eps\/4)cc B(x_oo,eps\/3)$ for large $i$, so by monotonicity formula, since
  $x_i in spt mu_(V_i)$, $
    mu_(V_i)(B(x_oo,eps\/3))>=mu_(V_i)(B(x_i,eps\/4))>=C>0
  , $ contradiction.

  Thus we proved for any $K$ and $eps$, there is a $N$ such that for $i>=N$, $
    d_"H" lr((K sect spt mu_(V_i),K sect spt mu),size:#12pt)<eps
  , $ #ie $spt mu_(V_i)->spt mu$ locally in Hausdorff distance.
]

= Allard Regularity Theorem
Roughly, the theorem says that: Suppose $V=(M,theta)$ rectifiable $n$-varifold has locally $L^p (mu_V)$ mean
curvature, $p>n$, $theta>=1$ $mu_V$-a.e. If $x in spt mu_V$ #st $
  (mu_V (B(x,r)))/(omega_n r^n) "sufficiently close to" 1
$ for some sufficiently small $r$ (depending on $norm(H)_(L^p)$), then $V$ $C^(1,1-n/p)$ near $x$.

- A key idea is to approximate $V$ locally by a graph of harmonic function.

== Harmonic approximation
Suppose $M cc RR^(n+k)$ is an smooth embedded $n$-manifold (may be weaken to $C^2$) with $H=0$, #ie minimal.
Wlog assume $0 in M$ and locally $M$ is a graph of $u:RR^n->RR^k$ with $nd u (0)=0$. Locally the area is $
  cal(A)_R (u)=int_(B(0,R))sqrt(det\(delta_(i j)+nd_i u dot.c nd_j u\))dd(x)
. $ For $abs(nd u)<eps_0$ small, Taylor expansion gives $
  cal(A)_R (u)=int_(B(0,R))1+1/2 abs(nd u)^2+F(nd u)dd(x)
, $ where $F$ is a real analytic map $RR^(n k)->RR$, and there is $C=C(n,k)$, such that $
  abs(F(P))<=C abs(P)^4, abs((nd F)(P)) <=C abs(P)^3,quad P=(P_(i j))_(n times k),abs(P)<eps_0
. $ $cal(A)_R$ is stationary under variation supported on $B(0,R)$, so we have $
  int_(B(0,R))sum_i nd_i u dot.c  nd_i vphi dd(x)=int_(B(0,R))sum_(i,j)A_(i j)(nd u)nd_i vphi^j dd(x),
  quad "where" A_(i j)=nd_(p_(i j))F
, $ for any $vphi:RR^n->RR^k$ supported on $B(0,R)$. Integrating by parts we get $
  lap u=sum_(i,j)a_(i j)(nd u)nd_i nd_j u,quad a_(i j)(P)=O(abs(P)^2)
. $ Hence if $abs(nd u)$ is small, $u$ is almost a harmonic function: Suppose $abs(nd u)<eps_0$ and let $v$
be the harmonic function that agrees with $u$ on $pt B(0,R)$, we have $
  int_(B(0,R))sum_i nd_i v dot.c nd_i vphi dd(x)=0,quad forall vphi in C_0^oo (B(0,R))
. $ Then $
  int_(B(0,R))sum_i nd_i (u-v)dot.c nd_i vphi=int_(B(0,R))sum_(i,j)A_(i j)(nd u)nd_i vphi^j dd(x)
. $ Let $vphi=u-v$ (#text(blue)[could do this since $u-v in H_0^1(B(0,R))$?]), we have $
  norm(nd (u-v))_(L^2 (B(0,R)))^2&=int_(B(0,R))sum_(i,j)A_(i j)(nd u)nd_i (u^j-v^j) \
  &<=sum_(i,j)norm(A_(i j)(nd u))_(L^2 (B(0,R))) norm(nd (u-v))_(L^2 (B(0,R)))
. $ Hence $
  norm(nd (u-v))_(L^2 (B(0,R)))^2<=sum_(i,j)norm(A_(i j)(nd u))_(L^2 (B(0,R)))^2
  <=C int_(B(0,R))abs(nd u)^6 dd(x)
. $ If $sup_(B(0,R))abs(nd u)=eps<eps_0$, we have $
  norm(nd (u-v))_(L^2)<=C eps^2 norm(nd u)_(L^2) "on" B(0,R)
. $ 

== Lipschitz approximation
Define the quantity _tilt excess_ $
  E(x_0,r,T)=1/r^n int_(B(x_0,r))abs(pi_(T_x M)-pi_T)^2 dd(mu_V)
, $ where $B(x_0,r)cc U$, $T cc RR^(n+k)$ an $n$-dim subspace and $pi_T$ is the orthogonal
projection map onto $T$. To see what this is, WLOG assume $T=RR^n times {0}$. Note that orthogonal projections
are symmetric matrices, write $pi_(T_x M)=(p_(i j))$ we have  $
  abs(pi_(T_x M)-pi_T)^2=tr (pi_(T_x M)^2+pi_(T_x M)^2-2pi_(T_x M)dot.c pi_T)
  =2n-2sum_(i=1)^n p_(i i)=2sum_(i=n+1)^(n+k)p_(i i)
. $ Note that $nd^M x^i=pi_(T_x M)e_i$, so $
  abs(nd^M x^i)^2=abs(pi_(T_x M)e_i)^2=sum_j p_(i j)^2=(p^t p)_(i i)=p_(i i)
, $ Hence $
  1/r^n int_(B(x_0,r))sum_(i=1)^k abs(nd^M x^(n+i))^2 dd(mu_V)=1/2 E(x_0,r,T)
. $ When $M$ is locally a graph of function $u$, this equals to the energy of $u$.

#lemma[
  Suppose $B(x_0,R)cc U$, then for any $n$-dim $T cc RR^(n+k)$ and $beta in (0,1)$ we have $
    1/R^n int_(B(x_0,beta R))abs(pi_(T_x M)-pi_T)dd(mu_V)
    <=C/R^n int_(B(x_0,R))abs(d(x,x_0+T)/R)^2 dd(mu_V)+C/R^(n-2)int_(B(x_0,R))abs(H)^2 dd(mu_V)
  , $ where $C=C(n,beta)$
] <allard-2-4>
#proof[
  WLOG assume $x_0=0$ and $T=RR^n times {0}$, let $
    X=eta(x)^2 x',quad x'=(0,...,0,x^(n+1),...,x^(n+k)),eta>=0 "chosen later"
  . $ Note that $
    div_M x'=sum_(i=n+1)^(n+k)p_(i i)=1/2 sum_(i j)abs(p_(i j)-eps_(i j))^2=1/2 abs(pi_(T_x M)-pi_T)^2=:F
  , $ where $(eps_(i j))$ is the matrix of $pi_T$. So $
    int_M F eta^2 dd(mu_V)=-int_M 2eta p_(i j) nd^i eta (x')^j+eta^2 x'dot.c H dd(mu_V)
  . $ Note that $eps_(i j)=0$ for $j>n$ and $(x')^j=0$ for $j<n$, we have $
    int_M F eta^2 dd(mu_V)&=-int_M 2eta (p_(i j)-eps_(i j)) nd^i eta (x')^j+eta^2 x'dot.c H dd(mu_V) \
    &<=int_M 2eta sqrt(2F) abs(nd eta)abs(x')+eta^2 abs(x')abs(H)dd(mu_V)
  . $ This gives (by $2a b<=a^2+b^2$) $
    int_M F eta^2 dd(mu_V)<=16int_M abs(x')^2 abs(nd eta)^2+abs(x')abs(H)eta^2 dd(mu_V)
  . $ Choose $eta==1$ on $B(0,beta R)$, supported on $B(0,R)$ and $abs(nd eta)<=2/((1-beta)R)$, using that $
    2abs(x')abs(H)<=abs(x')^2/R^2+R^2 abs(H)^2 quad "and" quad abs(x')=d(x,0+T)
  , $ we get the desired inequality.
]

Now we propose the *main assumption*: (Denote $mu_V=mu$ for simplicity). \
#h(2em)
Assume $theta>=1$ $mu$-a.e. in $U$,
$0 in spt mu$, $B(0,R)cc U$, and $
  (mu(B(0,R)))/(omega_n R^n)<=1+delta,quad R^(1-n/p)norm(H)_(L^p (B(0,R)))<=delta
, $ where $delta in (0,1/4]$ to be specified later.

Note that by the canonical representatives, we have $M_V=spt mu$ and
$Theta_V=Theta^n (mu,x)$ in place of $M,theta$. Since $Theta_V$ is upper semi-continuous, we have
$Theta_V>=1$ a.e. in $spt mu sect B(0,R)$.

By monotonicity formula, we have for any $x in B(0,2delta)$, $r<R'=(1-2delta)R$, $
  1-C_1 delta<= mu(B(x,r))/(omega_n r^n)<=(1+C_2 delta)mu(B(x,R'))/(omega_n (R')^n)
  <= (1+C_2 delta)/(1-2delta)^n mu(B(0,R))/(omega_n R^n)<=1+C_3 delta
. $ In particular, we have $
  Theta(x)<=1+C delta, quad forall x in spt mu sect B(0,2delta R)
. $ Also, the monotonicity gives $
  int_(B(x,(1-2delta)R)) abs((y-x)^perp)^2/abs(y-x)^(n+2)dd(mu(y))<=C delta,quad
  x in spt mu sect B(0,2delta R)
. $ 
#lemma(name:"Affine approximation")[
  If $delta<=1/16$, and the main assumption holds, then for any $x_0 in spt mu_V sect B(0,2delta R)$ and 
  $r_0<=4delta R$, there is an $n$-dim subspace $T=T(x_0,r_0)$ such that $
    sup_(spt mu_V sect B(x_0,r_0))d(x,x_0+T)<=C(n,k,p) delta^(1/(2n+2))r_0
  . $ 
]
- #text(blue)[Need $delta$ small enough?]
#proof[
  Since $delta<=1/16$, we have $2r_0<=8delta R<(1-2delta)^2 R$, apply above discussion to smaller ball
  $B(x_0,(1-2delta)R)cc B(0,R)$, thus for $delta<=delta_0$ small, $
    1/2<=1-C delta<= mu(B(x,r))/(omega_n r^n)<=1+C delta<=2,quad
    forall x in spt mu sect B(x_0,r_0),r<=2r_0
  . $ Also we have $
    int_(B(x,2r_0))abs(pi_(N_x M)(y-x))^2/(2r_0)^(n+2)dd(mu)
    <=int_(B(x,2r_0))abs(pi_(N_x M)(y-x))^2/abs(y-x)^(n+2)dd(mu)
    <=C delta
  . $ Let $0<alpha<1$ to be choose later, there are finitely many $xi_j in spt mu sect B(x_0,r_0)$ such
  that $B lr((xi_j,delta^alpha r_0\/2),size:#12pt)$ maximal disjoint, then $
    spt mu sect B(x_0,r_0)cc union.big_(j=1)^N B lr((xi_j,delta^alpha r_0),size:#12pt)
  . $ Then we have $
    (N omega_n delta^(alpha n)r_0^n)/2^(n+1)
    <=sum_(j=1)^N mu lr((B lr((xi_j,delta^alpha r_0\/2),size:#12pt)),size:#12pt)
    <=mu(B(0,2r_0))<=omega_n 2^(n+1)r_0^n
  . $ Hence $N<=4^(n+1) delta^(-alpha n)$. Now since $B(x_0,r_0)cc B lr((xi_j,2r_0),size:#12pt)$ we have $
    int_(B(x_0,r_0)) sum_j abs(pi_(N_x M)\(x-xi_j\))^2<=C N delta r_0^(n+2)=C' delta^(1-alpha n)r_0^(n+2)
  . $ By Markov's inequality, for any $K>0$ we have $
    sum_j abs(pi_(N_x M)\(x-xi_j\))^2<=C'' K delta^(1-alpha n)r_0^(n+2) quad "out of a set of" mu"-measure"<=1/K
  . $ Note that $mu(B(x_0,delta^alpha r_0))>=1/2 omega_n delta^(alpha n)r_0^n$. Let $K^(-1)=1/4 omega_n
  delta^(alpha n)r_0^n$, then there exists some $x_1 in B(x_0,delta^alpha r_0)$ such that $
    sum_j lr(abs(pi_(N_(x_1) M)\(x_1-xi_j\)),size:#16pt)^2<=C delta^(1-2alpha n)r_0^2
  . $ Hence $
    lr(abs(pi_(N_(x_1) M)\(x_1-xi_j\)),size:#16pt)<=C delta^(1/2-alpha n)r_0, forall 1<=j<=N
  . $ Note that $abs(x_1)<=delta^alpha r_0$, let $alpha=1/(2n+2)$, we get $
    lr(abs(pi_(N_(x_1) M)xi_j),size:#14pt)<=C lr((delta^(1/2-alpha n)+delta^alpha),size:#12pt)r_0
    =C delta^(1/(2n+2)) r_0 
  . $ Choose $T=T_(x_1)M$, we have shown that all $xi_j$ lie in the $\(C delta^(1/(2n+2))r_0\)$-neighborhood
  of $T$. By the definition of $xi_j$'s, we have $
    d(x,x_0+T)<=C delta^(1/(2n+2))r_0, quad forall x in B(x_0,r_0)
  . $ 
]
- #text(blue)[Does closed/open ball matter??]

#remark[
  Note that $mu(B(x_0,r_0))<=2 omega_n r_0^n$, Hölder inequality gives $
    r^(1-n/2)norm(H)_(L^2 (B(x,r)))<=C r^(1-n/p)norm(H)_(L^p (B(x,r)))
  . $ Let $T=T(x_0,r_0)$ as in lemma and apply @allard-2-4, we further have $
    &1/r_0^n int_(B(x_0,beta r_0))abs(pi_(T_x M)-pi_T)dd(mu_V) \
    &<=C/r_0^n int_(B(x_0,r_0))abs(d(x,x_0+T)/r_0)^2 dd(mu_V)+C (r_0^(p-n)
    int_(B(x_0,R))abs(H)^p dd(mu_V))^(2/p) \
    &<=C' delta^(1/(n+1))
  . $ 
]

#lemma(name:"Lipschitz approximation")[
  Let $delta<=1/4$, $L<=1$ fixed. Suppose the main assumption holds for $R=1$,
  $r<delta$ and $x_0 in B(0,delta)sect spt mu$, WLOG assume $T(x_0,4r)$ is
  parallel to $RR^n times {0}$. Then there is $beta=beta(n,k,p)<=1/16$ such that
  if $delta<=(beta L)^(2n+2)$, there is a Lipschitz function
  $f: B^n (x'_0,r)->RR^k$ (where $x'=\(x^1,...,x^n\)$) with $
    op("Lip")f<=L,quad sup abs(f(x')-f(x'_0))<=C delta^(1/(2n+2))r
  $ and $
    &(mu(B(x_0,r)sect (spt mu\\Gamma(f))))/r^n
    +cal(H)^n (B(x_0,r)sect (Gamma(f)\\spt mu)) \
    &<=C/(L^2 r^n)int_(B(x_0,3r))abs(pi_(T_x M)-pi_T)^2 dd(mu)
    <=C L^(-2) delta^(1/(n+1))
  . $ 
]
