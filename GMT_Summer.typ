#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "xcharter",
  heading-font: "",
  numbering: "1.1.",
)

#let ulcorner = {$⌜$}
#let urcorner = {$⌝$}
#let llcorner = {$⌞$}
#let lrcorner = {$⌟$}
#let spt = math.op("spt")
#let Union = math.union.big

#title(font: "")[
  *GMT Summer SLMath - Lecture a*
]

= 06/08
Suggested books:
- H. Federer, Geometric Measure Theory
- F. Morgan, GMT: a beginner's guide
- Krantz-Parks, Geometric Integrate Theory
- L. Simon, Introduction to GMT
- Giaquinta-Modica-Couček, Gartesian currents

== Notations
- Tensor spaces $T^(k,l)(V)=T(V)^(tens k)tens T^*(V)^(tens l)$.
- Alternating tensors $Lambda^k (V),Lambda_k (V)$, with exterior product. 

Fact: $eta_1 wed dots.c wed eta_k (v_1,...,v_k)=det(pari(v_i,w_j))_(i,j)$ 

- Simple $k$-forms: $omega=v_1^*tens dots.c tens v_k^*$. This is bijection 
  to oriented $k$-subspaces of $V$, #ie the oriented Grassmannian.
- $L^2$-norm $|v|=pari(v,v)^(1/2)$.
- Comass-norm: $omega in Lambda^k (RR^n)$, $
    norm(omega)^*:=sup{pari(w,v):v in Lambda_k (RR^n),v "simple",|v|=1}
  . $ 
- Mass-norm: $v in Lambda_k (RR^n)$, $
    norm(v):=sup{pari(w,v):v in Lambda^k (RR^n),norm(w)^*=1}
  . $ 

= 06/09
== Current
#definition[
  $U cc RR^n$ open, a $k$-dim differential form $omega$ is a map $
    omega:U-->Lambda^k (RR^n),quad
    x|->sum_(i=1)^n omega_I (x) dd(x^I),quad I=(i_1,...,i_k)
  $ with available regularity. And the exterior derivative is defined by $
    dd(#[]):Lambda^k (U)-->Lambda^(k+1)(U),quad
    dd(omega)=sum_(i=1)^k sum_(j=1)^n pt_j omega_I (x)dd(x^j)wed dd(x^I)
  . $ And the divergence $
    div omega:=sum_(i,j,I')g^(i j)nd_j omega_(i I')dd(x^(I')),quad
    I'=(i_1,...,i_(k-1))
  . $ $omega$ is called _closed_ if $dd(omega)=0$; _exact_ if $omega=dd(eta)$.
]
#definition[
  Pull-back $
    (f^* omega)(v_1,...,v_k):=omega(dd(f)(v_1),...,dd(f)(v_k))
  . $ Fact: $
    dd(f^*omega)=f^*dd(omega)
  . $ 
]
#definition[
  $S cc RR^n$ a $k$-dim embedded manifold, and orientation of $S$ is a 
  non-vanishing continuous map $
    tau:S->Lambda^k (T S),quad p|->tau(p) in Lambda^k (T_p S)
  . $ 
]
#theorem(name:"Stokes")[
  If $S cc RR^n$ is smooth oriented submanifold with boundary, then $
    int_S dd(omega)=int_(pt S)omega
  . $ In particular (divergence theorem), $
    int_S div X dd(V_g)=int_(pt S)X dot.c nu dd(sigma_g),quad 
    nu "outward normal of" pt S
  . $ 
]

#definition[
  The topology on $C_c^oo (U,Lambda^k (RR^n))$ is given by
  $lim_(i->oo)omega_i->omega_oo$ if and only if $exists K "compact"$ such that
  $forall i,op("spt")omega_i cc K$, and $forall ell in NN$, $
    lim_(i->oo)omega_i xarrow(C^ell (K)) omega_oo 
  . $ The topology is locally convex, translation invariant and Hausdorff.
]
#definition[
  Let $cal(D)^k (U)=C_c^oo (U,Lambda^k (RR^n))$, the space of current is the 
  dual space $cal(D)_k (U)=cal(D)^k (U)^*$, #ie continuous linear functionals,
  endowed with the weak-$*$ topology.
]
#remark[
  + 0-dim currents are distributions.
  + Vector fields are 1-dim currents.
  + $k$-dim oriented submanifolds are $k$-currents.
  + $k$-dim oriented distributions (foliations) are $k$-currents.
]
#definition[
  Let $T$ be a current. For a multi-vector $xi$, $
    T wed xi (eta):=T(iota_xi eta)
  . $ For a form $omega$, $
    T llcorner omega (eta):=T(eta wed omega)
  . $ For a function $f$, $
    f_*T (eta):=T(f^*eta)
  . $ And the boundary vector $
    pt T (eta)=T(dd(eta))
  . $ And differentiation $
    pt_i T(omega):=-T(pt_i omega)
  . $ 
]

= 06/10
== Current (continued)
#definition[
  Let $T$ be a current. Define $spt T$ as following: For $A$ open, $A sect spt T
  =OO$ if for any $omega$ supported on $A$, $pari(T,omega)=0$.

  #h(-2em)
  The mass of $T$ is defined by $
    bb(M)_V (T):=sup{pari(T,omega):omega in cal(D)^k (V),norm(omega)^*<=1}
  , $ on any $V cc U$ open. Mass is lower-semi continuous in w.r.t. the 
  weak-$*$ topology.
]

#remark[
  $pt pt T=0$ for any $T$. If $T=bracket.l.stroked S bracket.r.stroked$ for a 
  submanifold $S$, then $pt T=bracket.l.stroked pt S bracket.r.stroked$. And 
  $bb(M)(T)="Vol"(S)$.
]

#remark[
  Typically currents have infinite mass, analog to order $>0$ distributions
  have infinite integration.
]

#proposition[
  If $T in cal(D)_k (U)$ has locally finite mass, then by Riesz repr., there 
  exists $mu_T$ positive, locally finite measure and $tau:U->Lambda_k (RR^n)$,
  with $norm(tau)=1$ $mu_T$-a.e. #st $
    pari(T,omega)=int_U pari(tau,omega)dd(mu_T)
  . $ 
]
#remark[
  $T=0$ $iff$ $pt_i T=0,forall i$.
]
#theorem(name:"Constancy")[
  Suppose $U in RR^n$ connected open set, $T in cal(D)_n (U)$, $pt T=0$, 
  then $T=dd(x^1) wed dots.c wed dd(x^n)|_U$ up to constant multiple.
]

Let $rho_eps$ be the favorite mollifier family. Define $
  pari(T*rho_eps,omega)=pari(T,rho_eps*omega)
. $ 
#lemma[
  Write $T_eps:=T*rho_eps$ for short,
  + $T_eps->T$ as $eps->0$;
  + $pt_i T_eps=(pt_i T)_eps$;  
  + $T_eps in C^oo (RR^n,Lambda_k (RR^n))$ (weighted distributions (fo)).
  Further, let $
    F_eps (y):=pari(T,rho_eps (y-x)dd(x^1)wed dots.c dd(x^n))
  . $ Then $T_eps=F_eps e_1 wed dots.c wed e_n$.
]

#proof(name:"of constancy")[
  Convolution with $rho_eps$, use lemma.
]

#definition[
  For $T_1 in cal(D)_k (U_1)$, $T_2 in cal(D)_ell (U_2)$, $
    pari(T_1 times T_2,omega wed eta):=pari(T_1,pari(T_2,eta) omega)
  , $ and define to be zero if the dimension does not match.
]
#remark[
  - $pt (T_1 times T_2)=pt T_1 times T_2+(-1)^k T_1 times pt T_2$
  - $pt f_* T=f_* pt T$
]

= 06/11
== Homotopy formula
$U cc RR^n$, $f,g:U->RR^n$, $h$ homotopy from $f$ to $g$, $T in cal(D)_k (U)$.
Suppose $h|_([0,1]times spt T)$ is proper, then $h_* ((0,1)times T)$ is 
well-defined and in $cal(D)_(k+1)(RR^n)$, and $
  pt h_* ((0,1)times T)=g_* T-f_* T-h_* ((0,1)times pt T)
. $ One may choose $h(t,x)=(1-t)f(x)+t g(x)$, in this case $
  bb(M)(h_* ((0,1)times T))
  <=sup_(spt T)|f-g|sup_(spt T)(abs(nd f)+abs(nd g))^k bb(M)(T)
. $ 

#definition[
  A $k$-dim current is called normal if $
    MM(T)<oo quad "and" quad MM(pt T)<oo
  . $ $T$ is called locally normal if $T$ is normal on every open bounded subset.
  The space of normal currents is denoted by $NN_k (U)$
]

#theorem(name:"Riesz")[
  If $T$ is normal, then we can write:
  - $T=tau mu$, with $mu$ finite positive Borel measure and $norm(tau) in
    L^1_mu (U)$;
  - $pt T=tau' mu'$ with $mu',tau'$ same as above.
]
#remark[
  By means of Banach-Alaoglu theorem, Plateau's problem can be solved in the
  framework of normal currents. Given $Gamma$ $(k-1)$-dim current with finite 
  mass,
  + ${T in NN_k (U):pt T=Gamma}$ is non-empty;
  + $MM$ is lower semi-continuous;
  + $NN_k (U)$ is a dual.
]

#definition[
  Given $T in cal(D)_k (U)$, the flat semi-norm $
    F_flat (T)=inf{MM(R)+MM(S):T=R+pt S, R in cal(D)_k (U),S in cal(D)_(k+1)(U)}
  . $ $arrow.r.squiggly$ flat distance.

  The closure $ov(NN_k (U))^flat$ in $cal(D)_k (U)$ is called the flat chains,
  denoted by $FF_k (U)$.
]
#definition[
  Define $cal(P)_(k,K)(U)$ as the additive subgroup of $cal(D)_k (U)$
  generated by oriented simplexes with convex hull inside $K$. The $RR$-linear 
  space generated by $P_(k,K)(U)$ is called the space of polyhedral chains,
  denoted by $PP_(k,K)(U)$. Finally, $
    cal(P)_k (U)=Union_(K cc U)cal(P)_(k,K)(U)
  $ is called the group of integral polyhedral chains.
]
#definition[
  $T in cal(D)_k (U)$ is said to be an integer rectifiable current (with
  support in $K$) if $forall eps>0$, $exists W cc U$ open and $C cc W$ compact 
  and $f:W->U$ in $C^1$ (or Lip?) with $f(C)cc K$ #st $
    MM(T-f_* P)<eps quad "for some" P in cal(P)_(k,C)(W)
  , $ denoted by $cal(R)_(k,K)(U)$. And define $
    cal(R)_k (U)=Union_(K cc U)cal(R)_(k,K)(U)
  . $
]
#theorem[
  Let $T in cal(D)_k (U)$ with compact support, TFAE:
  + $T$ is an integer rect. current; #h(1fr)
  + $forall eps>0$, $exists W in RR^n$, $C cc W$ compact, $f:W->U$ Lip #st $
      MM(T-f_* P)<eps quad "for some" P in cal(P)_(k,C)(W)
    ; $ 
  + $exists Sigma$ $cal(H)^k$-rect. set, $Sigma cc spt T$, $eta:Sigma->Lambda_k
    (RR^n)$ that is $cal(H)^k llcorner Sigma$-summable #st $
      T=eta cal(H)^k llcorner Sigma
    , $ and for $cal(H)^k$-a.e. $x in Sigma$, $eta(x)$ is simple, spanning
    $T_x Sigma$ and $norm(eta) in NN$;
  + $MM(T)<oo$, and for $mu_T$-a.e. $x$ in $U$, $
      Theta_k (T,x) in NN, quad tau_T "is simple", quad 
      T_x (mu_T) "associated with" tau_T
    . $
  In this case, we can write $T$ as $
    pari(T,omega)=int pari(tau,omega)Theta_k (T,x)dd(mu_T)
    =int_Sigma pari(eta/norm(eta),omega)norm(eta)dd(cal(H)^k)
  . $ 
]
#remark[
  Let $T=f(x)dd(x^1)wed dots.c wed(x^n)$, then $
    MM(T)<oo iff T in L^1,quad MM(pt T)<oo iff |"d"f|(U)<oo
  . $ Hence $T$ is normal $=>$ $f in "BV"$.
]
#proposition[
  Suppose $T in cal(D)_k (RR^n)$, $pt T=0$, $spt T cc RR^k cc RR^n$, then 
  $T=lambda cal(H)^k llcorner RR^k$ for some $lambda in RR$.
]

= 6/12
#definition[
  A $k$-dim current $T in cal(D)_k (U)$ is called integral if $
    T in cal(R)_k (U) quad "and" pt T in cal(R)_(k-1)(U)
  , $ denoted by $cal(I)_k (U)$.
]
#remark[
  If $T in cal(R)_k (U)$, then $
    MM(T)=int_Sigma abs(Theta(x))dd(cal(H)^k)
  . $ 
]
#definition[
  Integral flat chains are defined by $
    cal(F)_k (U)={R+pt S:R in cal(R)_k (U),S in cal(R)_(k+1)(U)}
  . $ In this space we can introduce the flat metric $
    norm(T)_flat=inf{MM(R)+MM(S):T=R+pt S,R in cal(R)_k (U),S in cal(R)_(k+1)(U)}
  . $ One may check $
    norm(T_1+T_2)_flat<=norm(T_1)_flat+norm(T_2)_flat
  . $ 
]
#theorem(name:"Deformation")[
  Let $T in NN_k (RR^n)$, then for any $eps>0$, $
    T=P+pt R+S
  , $ where $P$ is polyhedral with support in $eps L_k$ ($k$-dim grid in $RR^n$),
  and $
    MM(P)&<=c MM(T),quad &MM(pt P)&<=c MM(pt T),\
    MM(R)&<=c eps MM(T),quad &MM(S)&<=c eps MM(pt T)
  . $ Moreover, let $A_eps$ be $eps$-neighborhood, $
    spt P union spt R &cc (spt T)_(2sqrt(n)eps) \
    spt pt P union spt S &cc (spt pt T)_(2sqrt(n)eps)
  . $ Finally,
  - If $T in cal(I)_k (RR^n)$, then $P,R$ are integral.
  - If $pt T in cal(R)_(k-1)(RR^n)$, then $S in cal(R)_k (RR^n)$.
  - If $T in cal(P)_k (RR^n)$, then $R in cal(P)_(k+1) (RR^n)$.
  - If $pt T in cal(P)_(k-1) (RR^n)$, then $S in cal(P)_k (RR^n)$.
]
#proof[
  See Simon or Krantz.
]

= 06/15
As corollaries of deformation theorem:
#theorem(name:"Isoperimetric ineq.")[
  Let $B in cal(I)_(k-1)(RR^n)$, $pt B=0$, then $exists T in cal(I)_k (RR^n)$
  with compact support #st $pt T=B$ and $
    MM(T)^(1/k)<=c(n,k)MM(B)^(1/(k-1))
  . $ Note that $B$ automatically has compact support.
]
#theorem(name:"Weak approximation")[
  Let $T in NN_k (RR^n)$, then $exists \{P_j\}_(j>=0)$ polyhedral chains and 
  $eps_j->0$ #st $
    P_j=sum_(F_j in L_(k,eps_j))theta_(F_j)F_j,quad 
    theta_(F_j)in RR
  , $ and $P_j->T$, $pt P_j->pt T$. Moreover if $T in cal(R)_k (RR^n)$,
  we have $theta_(F_j)in ZZ$.
]
#theorem(name:"Strong approximation")[
  If $T in cal(I)_k (RR^n)$, let $eps>0$, there exists $f:RR^n->RR^n$ bi-Lip 
  and a polyhedral chain $P$ with integer coefficient #st $
    MM(T-f_* P)+MM(pt T-f_* pt P)<eps
    , $ and $
    abs(f(x)-x)+abs(nd f-Id)<eps,quad forall x in RR^n
    . $ Moreover, $f(x)=x$ for any $x in.not (spt T)_eps$.
]

= 06/16
$
  cal(P)_k (U)&cc& cal(I)_k (U) &cc& cal(R)_k (U) &cc& cal(F)_k (U) \
  PP_k (U) &cc& NN_k (U) &cc& FF_k (U) sect {MM<oo} &cc& FF_k (U)
. $ 
#theorem(name:"FF compactness")[
  Let ${T_i}_(i>=0)cc cal(I)_k (RR^n)$ with $
    MM(T_i)+MM(pt T_i)<oo quad "uniformly on compact,"
  $ then there exists a subsequence $T_i->T in cal(I)_k (RR^n)$.
  Note that $MM$ is lower semi-continuous so $MM(T)<=liminf_(i->oo)MM(T_i)$.
]
#theorem(name:"AK compactness")[
  Let ${T_i}_(i>=0)cc NN_k (RR^n)$, rectifiable, with $
    MM(T_i)+MM(pt T_i)<oo,quad theta_(T_j)>=c quad "uniformly on compact,"
  $ then there exists a subsequence $T_i->T in cal(R)_k (RR^n)$ with
  $theta_T>=c$.
]
#proposition[
  Take $S$ a $k$-dim smooth submanifold and $S'$ $h$-dim submanifold where 
  $k+h>=n$. Then if $S$ intersects $S'$ transversally, then $S inter S'$
  is a $(k+h-n)$-dim smooth submanifold.
]
#proposition[
  If $S^k$ is smooth and $u:RR^n->RR^h$ is $C^1$, then for a.e. $y in img u$, $
    S_y:=S sect u^(-1)(y)
  $ is a smooth $(k-h)$-dim submanifold or empty.
]
#theorem(name:"Co-area formula")[
  Let $u:RR^n->RR^k$ Lip, then $
    int_(RR^n) f J_u dd(cal(H)^n)
    =int_(RR^k)int_(f^(-1)(y))f dd(cal(H)^(n-k))dd(y)
  , $ where $J_u=sqrt(det(dd(u)^T dd(u)))$.
]

Given $T in cal(R)_k (RR^n)$, with $T=(M,tau,theta)$. We want to intersect 
$T$ with the level set of $u:RR^n->RR$ Lip.
- $M$ is an $cal(H)^k$-measurable countably rect. set in $RR^n$, hence 
  $T_x M$ exists $cal(H)^k$-a.e.. #h(1fr)
- $nd^M u$ exists $cal(H)^k$-a.e., so we can define the good set $
    M_"good"={x in M:T_x M "exists and" lr((nd^M u),size:#14pt)_x!=0}
  . $ For a.e. $y in RR$ we define $
    M_y:=M_"good" sect u^(-1)(y)
  . $ 
- For orientation, observe that $forall x in M_"good"$, $
    T_x M={z+lambda nd^M u(x):z in T_x M_y,lambda in RR}
  . $ 
- By co-area formula, $
    pdv(,y)int_(M sect {u<y})lr(abs(nd^M u),size:#14pt)f dd(cal(H)^k)
    =int_(M_y)f dd(cal(H)^(k-1))
  . $ 
- Adjust the multiplicity $
    theta_+ (x)=cases(
      0\, quad & nd^M u=0,
      theta(x)\, quad & nd^M u!=0.
  ) $  
Hence, for a.e. $t$, we can define $
  T_y=T sect u^(-1)(y)=(M_y,theta_+ llcorner M_y, tau_y),quad 
  tau_y=tau llcorner (nd^M u)/abs(nd^M u)
. $
#proposition[
  + $cal(H)^(k-1)((M sect u^(-1)(y))\\M_"good")=0$. #h(1fr)
  + $M_y$ is $(k-1)$-rect. for a.e. $y$.
  + $T_x M_y=span tau_y$.
  + We have $
      int_RR MM lr((T_y),size:#14pt)dd(y)
      =int_RR int_(M_y)theta dd(cal(H)^(k-1))dd(y)=int_M theta
      lr(abs(nd^M u),size:#14pt) dd(cal(H)^k)<=(op("Lip")u) MM(T)
    . $ (Note $theta$ could be assumed to be non-negative).
  + If $T in NN_k (RR^n)$, then for a.e. $y$, $
      T_y=pt(T llcorner {u<y})-(pt T)llcorner {u<y}
    . $ (Easy to see for $T$ rect. use weak polyhedral approx. and 1st part of 
    slicing lemma for general $T$ normal).
  + If $T in cal(I)_k (RR^n)$, then for a.e. $y$, $
      pt T_y=(pt T)_y
    . $
]
#proof[
  See Simon.
]

= 06/17
#lemma(name:"Slicing")[
  Let ${T_i}_(i>=0)cc NN_k (RR^n)$ with uniformly bounded $MM(T)+MM(pt T)$,
  $T_i->T$, and $u:RR^n->RR$ Lip. Then for a.e. $y in RR$, there exists a 
  subsequence $T_i$ such that  $
    T_i sect u^(-1)(y)->T sect u^(-1)(y)
  . $ Moreover, $MM(T_i sect u^(-1)(y))+MM(pt T_i sect u^(-1)(y))$ is 
  uniformly bounded, it also converges to 0 if $MM(T_i)+MM(pt T_i)->0$.
]
#theorem(name:"Closure")[
  If ${T_i}_(i>=0)cc cal(R)_k (U)$, with $MM(T_i)+MM(pt T_i)$ uniformly bounded 
  on compact. Suppose $T_i->T$ in $cal(D)_k$ sense. Then $T in cal(R)_k (U)$.
]
#remark[
  This means that $cal(R)_k sect NN_k$ is weakly sequential closed.
]
#lemma(name:"Fundamental")[
  Let $T in cal(D)_k (RR^n)$, with locally finite mass. Assume $pt T=0$,
  $u$ Lip function and for a.e. $y$, $
    T sect u^(-1)(y)=pt(T llcorner{u<y}) in cal(R)_(k-1)(RR^n)
  . $ Then $T in cal(R)_k$.
]
#theorem(name:"Boundary rectifiability")[
  Let $T in cal(R)_k (RR^n)sect NN_k (RR^n)$, then we have 
  $pt T in cal(R)_(k-1)(RR^n)$. #ie, $ 
    cal(I)_k (RR^n)=cal(R)_k (RR)^n sect NN_k (RR^n)
  . $
]
#proof[
  We prove this (BR) together with the closure theorem (CL).

  - $k=0$ both are trivial.
  
  - To prove BR for case $k$, by weak polyhedral approx. (deformation theorem),
    take $cal(P)_k in.rev P_i->T$ with uniformly bounded $MM(P_i)+MM(pt P_i)$.
    Note that $pt P_i in cal(R)_(k-1)$, apply CL for $k-1$ to ${pt P_i}$ we see
    $pt T$ is rectifiable.

  - To prove CL for case $k$, by BR for $k$ we see $pt T_i in cal(R)_(k-1)$,
    hence by CL for $k-1$ applied to ${pt T_i}$, $pt T in cal(R)_(k-1)$.
    By isop. ineq., $exists S in cal(R)_k$ #st $pt S=pt T$. Replace $T_i$ by
    $T_i-S$ we may assume $pt T=0$.

    By slicing lemma (for $u=r$), up to subsequence, $
      T_i sect {r=R}-->T sect {r=R}
    . $ Apply CL for $k-1$ to $T sect {r=R}$, we see $T_(r=R)in cal(R)_(k-1)$.
    By fundamental lemma we are done.
]
#theorem(name:"Jerrard")[
  Let $T in NN_k (RR^n)$, $u:RR^n->RR^h$ Lip. Denote by $X$ the space 
  of $k-h$ currents with flat norm, then the map $
    RR^h-->X,quad y|-->T sect u^(-1)(y)
  $ is BV.
]
#theorem(name:"AK")[
  If $T in NN_k (RR^n)$, assume for any projection $p$ onto $k$-dim coordinate
  planes, $T sect p^(-1)(y)$ are integral for a.e. $y$, then $T in cal(R)_k
  (RR^n)$.
]

#definition[
  For $T in cal(I)_k (M)$ where $(M^n,g)$ is Riemannian manifold. $T$ is 
  said to be area-minimizing in $Omega cc M$ if $
    MM(T)<=MM(T+pt S),quad forall  S in cal(I)_(k+1),spt S cc Omega
  . $ 
]
By Federer-Fleming's compact theorem, every integral homology class of $M$
is represented by an area-minimizing (boundary free) current.

#remark[
  Assume $B in cal(I)_(k-1)(RR^n)$ with $pt B=0$, take $T in cal(I)_k (RR^n)$
  with $pt T=B$ area-minimizing. Put $
    V_T (A)=mu_T ({x in RR^n:(x,v) in A,v wed tau_T=0}),quad
    forall A cc op("Gr")(n,k) #text(red)[??]
  . $ Then $V_T$ is a $k$-dim integer multi. varifold and $mu_(V_T)=mu_T$, and $
    delta V_T (X)<=int abs(X wed tau_B)dd(mu_B)
  . $ 
]
#proof[
  Let $h_t$ be the homotopy generated by $X$, $h_0=Id$. We may choose $
    h(t,x)=x+t X(x)
  . $ Then $
    pt h_* ((0,t)times T)=h_(t*)T-T-h_*((0,t)times B)
  . $ Hence $
    pt(h_(t*)T-h_*((0,t)times B))=pt(T+pt(dots.c))=B
  . $ By area-minimizing, $
    MM(T)<=MM(h_(t*)T-h_*((0,t)times B))<=MM(h_(t*)T)+MM(h_*((0,t)times B))
  . $ Hence $
    MM(h_*((0,t)times B))<=int_0^t int abs(pt_t h_t wed nd h_t (tau_B))
    dd(mu_B)dd(t)
  , $ and $
    MM(h_(t*)T)=mu_(h_(t*)V)(RR^n)quad "for small" t
  . $ 
]
#definition[
  Given an area-mini. $T in cal(I)_k (M)$, the regular points $op("reg")(T)$ of
  $T$ is the set of $p in spt(T)sect Omega\\ spt pt T$ such that, $exists B 
  in.rev p$ open ball, $Sigma cc B$ a smooth orientable $k$-dim submanifold
  without boundary, and there is $c in NN$, $T llcorner B=c Sigma$.
]
#remark(name:"Codimension 1")[
  Let $(M^(n+1),g)$ Riemannian manifold of $C^(2,alpha)$, $T in cal(I)_n (M)$
  area-mini., then
  - $dim(op("sing")(T))<=n-7$ (Almgren, De Giogi, Federer, Fleming, Simons).
  - $op("sing")(T)$ is $(n-7)$-rectifiable (Simon).
  - $op("sing")(T)$ has locally finite $cal(H)^(n-7)$ measure (Naber-Valtorta).
  $n-7$ is sharp by Simons' cone (by variation calculation or a calibration).
]
#remark(name:"Larger codimension")[
  Let $(M^(n+k),g)$, $T$.
  - $dim(op("sing")(T))<=n-2$ (Almgren, De Lellis, Spadaro).
  - $op("sing")(T)$ is $(n-2)$-rectifiable & more
    (De Lellis-Minter-\??, K??-W??).
  - Still open if it is locally finite.
  - Example for any fractal set of dim $<n-2$ as singular set.
  - If $n=2$, then $op("sing")(T)$ is isolated
    (Chang, De Lellis-Spadaro-Spolaor).
  $n-2$ is sharp since: Holomorphic subvarieties are calibrated, hence
  area-mini.. Example: $lr({z^2=w^3},size:#14pt)cc CC^2 iso RR^4$.
]

#remark(name:"Boundary regularity")[
Want to estimate $op("reg")(pt T)$
- $M=RR^n$, $pt T cc$ boundary of a uniformly convex set, then 
  $op("sing")(pt T)=OO$ (Allard).
- In codim 1, $op("sing")(pt T)=OO$ (Hardt-Simon).
- Counterexample by Gulliver, De Lellis-De Philippis-Hirsch.
- $op("reg")(pt T)$ is dense in $spt pt T$
  (De Lellis-De Philippis-Hirsch-Massaccesi).
]
#remark(name:[Current $mod p$])[
  - $dim(op("sing")(T))<=n-1$.
  - if $p$ odd then it is $cal(H)^(k-1)$-rect. with locally finite measure.
]

#theorem(name:"Calibration")[
  $phi in C^oo (U,Lambda^k (RR^n))$ is called a calibration if 
  + $dif compose phi=0$;
  + $forall x$, $norm(phi(x))^*<=1$.
]
#example[
  Let $u$ solves MSE: $
    div((nd u)/sqrt(1+abs(nd u)^2))=0
  . $ Then $
    ((dd(x)wed dd(y)wed dd(z))llcorner nd (z-u(x,y)))/sqrt(1+abs(nd f)^2)
  $ is a calibration (locally).
]
#definition[
  Given a $k$-calibration $phi$ and a $k$-rect. current $T$ (with possible real 
  multiplicity), then $T$ is called calibrated if for any $x in spt T$, $
    pari(tau_T (x),phi(x))=1
  . $ 
]
#theorem[
  If $T$ is calibrated, then $T$ is area-mini.
]
#proof[
  Suppose $T$ is calibrated by $phi$, then, $
    MM(T)=pari(T,phi)=pari(T+pt S,phi)<=MM(T+pt S)
  . $
]
#theorem[
  Let $omega$ be the standard Kähler form on $CC^n$, then $1/k! omega^k$
  is a calibration.
]
