#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  heading-font: "",
  numbering: "1.1.",
)

#let ulcorner = {$⌜$}
#let urcorner = {$⌝$}
#let llcorner = {$⌞$}
#let lrcorner = {$⌟$}
#let spt = math.op("spt")
#let Union = math.union.big
#let sorry = emph[Sorry]

#title(font: "")[
  *GMT Summer SLMath - Lecture d*
]

= 06/08
== Radon measures
Think all $X$ to be $RR^n$ in the following.

#definition[
  Outer measures on a set $X$ are $
    mu:cal(P)(X)->[0,oo]
  $ such that:
  - $mu(OO)=0$;
  - $mu(A)<=sum_k mu(A_k)$ if $A cc union.big_k A_k$.
]
#definition[
  $A cc X$ is $mu$-measurable if $forall B in X$, $
    mu(B)=mu(B sect A)+mu(B\\A)
  . $ 
]
#theorem[
  $mu$-measurable subsets form a $sigma$-algebra and $mu$ is a "classical"
  measure on them.
]
Hence we could define measurable functions, Lebesgue integral, convergence 
theorems, products (Fubini), ...

#definition[
  $mu$ is Borel on $RR^n$ if the Borel sets are $mu$-measurable. It is regular
  if $forall A cc X$, there is $B cc A$ $mu$-measurable #st $A cc B$
  and $mu(A)=mu(B)$. It is called Borel regular if $B$ could be chosen Borel.

  $mu$ is called a Radon measurable if it is Borel regular and locally finite.
]
#remark[
  A Borel regular measure restricted on finite measure subsets is Radon.
]
#theorem(name:"Fundamental")[
  + If $mu$ is Borel, $B$ measurable $mu(B)<oo$, then for all $eps>0$,
    $exists C cc B$ closed #st $mu(B\\C)<eps$.
  + If $mu$ is Radon, $B$ measurable, then for all $eps>0$, $exists U supset B$
    open #st $mu(U\\B)<eps$.
]
We have Lusion, Egorov for Radon measures.
#theorem[
  If $mu$ is an outer measure and $mu(A union B)=mu(A)+mu(B)$ whenever $
    d(A,B)=inf_(x in A,y in B)|x-y|>0
  , $ then $mu$ is Borel.
]
#definition[
  A "signed measure" is an $RR^k$-valued measure consists of 
  + $mu$ a Radon measure of $RR^n$;
  + $f in L_"loc"^1 (X,mu,RR^k)$ (Borel measurable and with finite $L^1$ on 
    compact).
]

#theorem(name:"Riesz representation")[
  $L:C_c^0 (RR^n,RR^k)->RR$ is a linear functional #st $
    forall K "compact",quad sup{L(f):norm(f)_oo<=1,spt(f)cc K}<oo
  . $ Then there exists $mu$ Radon, $sigma in L_"loc"^1 (RR^n,mu,RR^k)$ #st $
    L(f)=int f sigma dd(mu)
  . $ $(mu,sigma)$ is unique if we require $abs(sigma)=1$ $mu$-a.e..
]

== Covering theorems
#theorem(name:"Vitali covering")[
  Let $cal(F)$ be a collection of closed balls with uniformly bounded radii,
  then there exists a (countable) subcollection $cal(G)$ of pairwise disjoint
  balls #st $
    union.big_(B in cal(F))B cc union.big_(B in cal(G))5B'
  . $ 
]
#corollary[
  Let $W cc RR^n$ open, then there exists a countable collection $cal(B)$ of
  pairwise disjoint balls in $W$ #st $
    cal(L)^n lr((W\\union.big_(B in cal(B))B),size:#16pt)=0
  . $ 
]
#theorem(name:"Besicovitch covering")[
  There exists an $N(n)$ such that: If $cal(F)$ is a collection of closed 
  balls with uniformly bounded radii, then there exists $cal(G)_1,...,cal(G)_N$,
  subcollections of pairwise disjoint balls and $
    {"centers of" B:B in cal(F)}cc Union_(i=1)^N Union_(B in cal(G)_i)B
  . $ 
]
#corollary[
  Let $A$ be a $mu$-measurable set for Radon measure $mu$ on $RR^n$.
  Assume $cal(F)$ is a fine cover of $A$ (every $x in A$ is a center of some 
  ball) by closed balls. Then there exists a pairwise disjoint  subcollection
  that covers $A$ $mu$-a.e..
]

= 06/09
== Differentiation theorems
#definition[
  Given two Radon measures $mu$, $nu$, $
    ov(D)_mu nu(x):=limsup_(r->0)(nu(B(x,r)))/(mu(B(x,r))), quad
    underline(D)_mu nu(x):=liminf_(r->0)(nu(B(x,r)))/(mu(B(x,r)))
  . $ 
]
#theorem[
  We can always write $nu=nu_"ac"+nu_"s"$ where $
    nu_"ac"<<mu, quad nu_"s" perp mu
  . $ Moreover, $
    ov(D)_mu nu(x)=underline(D)_mu nu(x)<oo "for" mu"-a.e." x
  , $ and $
    nu_"ac" (A)=int_A D_mu nu dd(mu),quad forall A "Borel"
  . $ 
]
#remark(name:"Extremely useful")[
  For $mu$ vector valued measure, $
    f(x)=lim_(r->0)1/(mu(B(0,r)))int_(B(0,r))f dd(mu)quad "for" mu"-a.e." x
  . $ For $mu perp alpha$, then for $mu$-a.e. $x$, $
    (alpha(B(x,r)))/(mu(B(x,r)))->0 quad "as" r->0
  . $ 
]
#lemma[
  + $A cc {underline(D)_mu nu(x)<=alpha}$ $=>$ $nu(A)<=alpha mu(A)$.
  + $A cc {ov(D)_mu nu(x)>=alpha}$ $=>$ $nu(A)>=alpha mu(A)$.
]
#proof[
  1. Choose any open set $U supset A$, $eps>0$, let #h(1fr) $
    cal(F):={B(x,r):x in A, nu(B(x,r))<=(alpha+eps)mu(B(x,r))}
  . $ Cover $nu$-a.e. $A$ with disjoint ball is $cal(F)$, cover $=:cal(G)$.
  Then $
    nu(A)<=sum_(B in cal(G))nu(B)<=(alpha+eps)sum_(B in cal(G))mu(B)
    <=(alpha+eps)mu(U)
  . $ Let $U->A$ and $eps->0$ we see $nu(A)<=alpha mu(A)$.
  2. Similar.
]
#proof(name:"of main theorem")[
  Fix $a<b$, let $
    A={x:underline(D)_mu nu(x)<=a<b<=ov(D)_mu nu(x)}sect B_R
  . $ By lemma, $
    b mu(A)<=nu(A)<=a mu(A)
  . $ Hence $mu(A)=0$.

  Let $A_k={ov(D)_mu nu<k}$. Then for $A cc A_k$, $nu(A)<=k mu(A)$. Hence $
    nu llcorner {ov(D)_mu nu<oo}=nu llcorner Union_(k>=0)A_k<<mu
  . $ Let $
    nu_"ac"=nu llcorner {ov(D)_mu nu<oo},quad nu_"s"=nu-nu_"ac"
  . $
]
#lemma[
  If $alpha<<mu$, then $
    alpha(A)=int_A D_mu alpha dd(mu)
  . $ 
]
#proof[
  Let $
    A'=Union_(k in ZZ)A sect {t^k<=D_mu alpha<=t^(k+1)}
  . $ Note $A_(-oo)$ and $A_oo$ are $alpha$-null. So $
    sum_k t^(-1)int_(A_k)D_mu alpha dd(mu)
    <=sum_k t^k mu(A_k)<=alpha(A)<=sum_k t^(k+1) mu(A_k)
    <=sum_k t int_(A_k)D_mu alpha dd(mu)
  . $ Let $t=1+eps$, $eps->0$.
]

== Hausdorff measures
#let Hs = $cal(H)^s$
#let Hn = $cal(H)^n$
#definition[
  Fix any $s>=0$, $A cc RR^n$, $delta in (0,oo]$, define  $
    cal(H)_delta^s (A)=inf_({C_i}){sum_(i=1)^oo omega_s ((op("diam")(C_i))/2)^s:
    A cc Union_i C_i, op("diam")(C_i)<=delta}
  . $ Note that this is monotone decreasing in $delta$. We define $
    cal(H)^s (A)=lim_(delta->0) cal(H)_delta^s (A)
  . $ 
]
#lemma[
  $Hs$ is an outer measure, and if $d(A,B)>0$, then $
    Hs(A union B)=Hs(A)+Hs(B)
  . $ This makes $Hs$ a Borel regular measure.
]
#lemma[
  If $f:RR^n->RR^m$ Lip, then $
    Hs(f(A))<=(op("Lip")f)^s Hs(A)
  . $ 
]

Take a Radon measure $mu$, define $
  Theta_k^* mu=limsup_(r->0) mu(B(x,r))/(omega_k r^k),quad
  Theta_(k*) mu=liminf_(r->0) mu(B(x,r))/(omega_k r^k)
. $ 
#theorem[
  $mu$ Radon measure, $B$ Borel, then 
  + $Theta_k^* (mu,x)>=t$, $forall x in B$ $=>$ $mu(B)>=t cal(H)^k (B)$
  + $Theta_k^* (mu,x)<=t$, $forall x in B$ $=>$ $mu(B)<=2^k t cal(H)^k (B)$
]
#proof[
  See Leon Simon.
]

= 06/10
#theorem(name:"Rademacha")[
  $U cc RR^n$ open, $f:U->RR$ Lip, then $f$ is differentiable a.e..
]
#lemma[
  $"Lip"=W^(1,oo)$.
]
#proof(name:"of Rademacha")[
  - Differentiation at $x_0$ is equivalent to #h(1fr) $
      v_(x_0,h)(y):=(u(x_0,+h y)-u(x_0))/h xarrow("locally uniformly") (y|->L y)
    , $ for $L$ linear.
  - $v_(x_0,h)$ is equiv-Lipschitz. So there is subsequence
    $v_(x_0,h_j)->bar(v)$ convergent locally uniformly. If $bar(v)$ is a linear 
    function that does not depend on the subsequence, then $u$ is differentiable
    at $x_0$.
  - $pt_(y^j)v_(x_0,h)(y)=pt_(x^j)u(x_0+h y)$.

  Choose $x_0$ a Lebesgue point of distribution derivative, then $
    int_(B(x_0,R))abs(pt_(y^j)v_(x_0,h)-pt_(x^j)u(x_0))dd(y)
    &=int_(B(x_0,R))abs(pt_(x^j)u(x_0+h y)-pt_(x^j)u(x_0)) \
    &=1/h^k int_(B(x_0,R h))abs(pt_j u(z)-pt_j u(x_0))dd(z) \
    &->0 quad "as" h->0
  . $ 
  Hence $pt_(y^j)bar(v)=pt_(x^j)u(x_0)$ in the distribution sense.
  Easy to prove $bar(v)(y)=sum_j pt_j u(x_0) y_j$ is linear.
]
#theorem(name:"Whitney")[
  If $K cc RR^n$ compact and $u:K->RR$ #st 
  + $u$ differentiable everywhere;
  + $dd(u)$ is continuous;
  + $limsup_(delta->0){abs(u(y)-u(x)-dd(u)(x)dot.c(y-x))/abs(y-x):
    x!=y in K,abs(x-y)<=delta}=0$
  Then there exists a $C^1$ extension of $u$ to $RR^n$.
]
#corollary[
  For $u:B^n (0,1)->RR$ Lip, then for any $eps>0$, there exists $v in C^1$ #st $
    cal(L)^n ({u!=v})<eps
  . $ 
]
#proof[
  #sorry
]
#proposition[
  Let $Omega cc RR^k$ open, $k<=n$,
  + If $u:Omega->RR^n$ is Lip, then #h(1fr) $
        cal(H)^k (u(A))<=(op("Lip")f)^k cal(L)^k (A)
    . $ 
  + (Sard's theoerm) If $u$ is $C^1$, then $
        cal(H)^k (u({rank dd(u)<k}))=0
    . $ 
  + If $u$ is $C^1$ diffeomorphism onto its image, then $
      cal(H)^k (u(Omega))=int_Omega sqrt(det(dd(u)^T dd(u)))
    . $ 
]

= 06/11
#lemma[
  If $n>=k$, $f:Omega (cc RR^k)-> RR^n$ is $C^1$, injective, $rank dd(f)=k$,
  $A cc Omega$ Borel, then $
    int_(f(A))card f^(-1)(y)dd(cal(H)^k (y))=int_A sqrt(det(dd(f)^T dd(f)))
  . $ 
]
#proof[
  See Leon Simon.
]
#remark[
  Same formula holds if $f$ is merely locally Lip.
]

Consider $M$ a $C^1$ submanifold, $mu=cal(H)^k llcorner M$, let $
  mu_(x_0,eps)=(lambda_(x_0,eps))_*mu,quad lambda_(x_0,eps)=eps^(-k)(x_0+eps y)
. $ Then $mu_(x_0,eps)->cal(H)^k llcorner T_(x_0) M$ weakly as $eps->0$.

Recall that a (countably) rectifiable set is $
  M=M_0 union Union_(i=1)^oo M_i,quad cal(H)^k (M_0)=0,quad
  M_i cc N_i,N_i "be" C^1 "graphs"
. $ 

#theorem[
  Take $mu=f cal(H)^k llcorner M$, $M$ rectifiable with locally finite $cal(H)^k$
  measure. Then for $cal(H)^k$-a.e. $x_0 in M$, there exists a $k$-dim affine 
  subspace $Pi_(x_0)$ through $x_0$ #st $
    mu_(x_0,r)-->f(x_0)cal(H)^k llcorner Pi_(x_0),quad r->0
  . $ 
]
#proof[
  By Besicovitch differentiation theorem, since $mu llcorner M_i perp (mu-mu 
  llcorner M_i)$, let $alpha=mu-mu llcorner M_i$, $
    lim_(r->0) (alpha(B(x,r)))/(mu(B(x,r)sect M_i))
  , $ for $cal(H)^k$-a.e. $x in M_i$. Hence $
    mu_(x_0,r)-(mu llcorner R_i)_(x_0,r)-->0 quad
    "for" cal(H)^k"-a.e." x_0 in R_i
  . $ WLOG assume $M cc N_i$ $C^1$ graph. WLOG $M$ is the whole graph.
  Use Lusin to make $f$ continuous and conclude.
]
#corollary[
  $mu$ as before, then $
    Theta_k (mu,x)=lim_(r->0) mu(B(x,r))/(omega_k r^k)=f(x)quad 
    "for" mu"-a.e." x
  . $ 
]
#theorem[
  Fix $k<=n$, if $mu$ is a Radon measure, and for $mu$-a.e. $x$, $
    mu_(x,r)-->c_x cal(H)^k llcorner Pi_x
  , $ for some plane $Pi_x$, $c_x>0$, as $r->0$. Then there exists $M$
  rectifiable and $f:M->oo$ Borel #st $
    mu=f cal(H)^k llcorner M
  . $ 
]
This is implied by:
#theorem(name:"Rectifiability criterion")[
Assume $
  Theta_(k*)(mu,x)=liminf_(r->0) mu(B(x,r))/(omega_k r^k)>0 quad
  "for" mu"-a.e." x
  , $ and assume $forall x$, there exists $alpha_x<pi/2$ and $k$-dim plane $Pi_x$
  and cone $
  C(x,Pi_x,alpha_x)={y:lr(abs("Proj"_(Pi_x^perp)(y-x)),size:#16pt)
  <=tan alpha_x lr(abs("Proj"_(Pi_x)(y-x)),size:#16pt)}
, $ such that $
  lim_(r->0) mu(B(x,r)\\C(x,Pi_x,alpha_x))/(omega_k r^k)=0
. $ Then there exits $M$ $k$-rectifiable #st $mu(M^c)=0$.
]
#lemma[
  Let $E cc RR^n$ such that there is fixed $Pi_0,alpha_0$ such that $
    E cc C(x,Pi_0,alpha_0), quad forall x in E
  . $ Then $E cc $ graph of $f:Pi_0->Pi_0^perp$ Lip with Lip constant controlled
  by $tan alpha_0$.
]

= 06/12
#proof(name:"of criterion")[
  There exist ${P_i}_(i>=0)cc op("Gr")(k,n)$ dense. For any $P,alpha$, there
  exists $P_i$, and $alpha_j in QQ$ such that $C(0,P,alpha)cc C(0,V_i,alpha_j)$.
  Consider $
    A_(i,j)&={x:limsup_(r->0)mu(B(x,r)\\C(x,V_i,alpha_j))/r^k=0} \
    A_(i,j,ell)&={x in A_(i,j):liminf_(r->0)mu(B(x,r))/(omega^k 2^k)>1/ell}
  . $ Then $
    mu lr((RR^n\\Union_(i,j,ell)A_(i,j,ell)),size:#16pt)=0
  . $ Now fix a small number $eta(i,j,ell)>0$, fix $h in NN_(>0)$. Let $
    A_(i,j,ell,h)={x:mu(B(x,r)\\C(x,V_i,alpha_j))/r^k<eta(i,j,ell),
    mu(B(x,r))/(omega^k 2^k)>1/ell,forall r<1/h}
  . $ Then $forall z$, $E=A_(i,j,ell,h)sect B(z,1/(4h))$ is a Lip graph by the
  claim below, provided by $eta<<1/ell$. Let $beta_j=1/2(alpha_j+pi/2)$.
  Claim that $
    E\\C(x,P_i,beta_j)=OO,quad forall x in E
  . $ To see this, pick any $y in E\\C(x,P_i,beta_j)$, then there is a $rho$
  #st ($2r<1/(2h)$) $
    B(y,rho) cc B(x,2r)\\C(x,V_i,alpha_j),quad rho>=c(alpha_j)r
  . $ Then $
    mu(B(x,2r)\\C(x,V_i,alpha_j))<eta (2r)^k \
    mu(B(y,rho))>=omega_k/ell rho^k>=omega_k/ell (c(alpha_j))^k r^k
  . $ This is false when $eta$ is too small.
]
== Varifolds
#definition[
  A general $k$-dim varifold $V$ in $U cc RR^n$ open is a Radon measure on
  $op("Gr")(k,n)times U$. And define $mu_V (A)=V(op("Gr")(k,n)times A)$.
]
#theorem(name:"Disintegration")[
  Given $V$ general varifold, $exists eta_x^V$ family of prob. measures on
  $"Gr"(k,n)$ #st $
    int_("Gr"(k,n)times U)phi(P,x)dd(V(P,x))
    =int_U int_("Gr"(k,n))phi(P,x)dd(eta_x^V (P))dd(mu_V (x))
  . $ 
]
#remark[
  A smooth $M$ induces a varifold by $
    V=delta_(T_x M)tens cal(H)^k llcorner M
  . $ 
]
#definition[
  A varifold $V$ is said to be rectifiable if there is a rectifiable set $M$,
  and a Borel function $Theta:M->RR_(>0)$ such that $
    V=delta_(T_x M)tens Theta(x) cal(H)^k llcorner M
  . $ It is said to be #strong[integer rectifiable] if $Theta(x)in NN_(>0)$ for
  $cal(H)^k$-a.e. $x in M$.
]
#definition[
  If $Phi:RR^n->RR^n$ is diffeomorphism, then $
    Phi_*(delta_(T_x M)tens Theta(x) cal(H)^k llcorner M)
    :=delta_(T_y Phi(M))tens Theta compose Phi^(-1)(y) cal(H)^k llcorner Phi(M)
  . $ And define the mass of $V$ by $
    norm(V):=int_M Theta dd(cal(H)^k)
  . $ 
]
#theorem[
  Let $X$ be a variational vector field, then $
    delta V(X):=lr(dv(,t)|)_(t=0)norm((Phi_t)_* V)
    =int_M div^M X dd(mu_V)
  , $ where $mu_V:=Theta cal(H)^k llcorner M$, and $
    div^M X:=e_i dot.c nd_(e_i) X, quad {e_i} "O.N.B. of" T_x M
  . $ 
  $V$ is said to be stationary if the variation is 0 for any $X in C_c^oo$.
]
#theorem[
  $V$ is said to have generalized mean curvature $H in L^p$ if there exists 
  $H in L^p (mu_V,RR^n)$ such that for any $X in C_c^oo$, $
    int_M div^M X dd(mu_V)=-int_M H dot.c X dd(mu_V)
  . $ 
]
#theorem(name:"Allard compactness")[
  Let ${V_j}_(j>=0)$ is a sequence of stationary integer rectifiable
  $k$-varifolds in $U cc RR^n$, with uniformly bounded mass. Then there exists
  a convergent subsequence in weak-$*$ to a stationary integer rectifiable
  $V_oo$.
]
