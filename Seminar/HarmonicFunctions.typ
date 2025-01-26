#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  numbering: "1.1.",
)

#align(center)[#text(20pt)[
  *Properties of Harmonic Functions*
]#v(0.5cm)]

Through out this note, we use $laplace$ as the standard Laplacian operator,
$Omega$ on an open connect subset of $RR^n$, $n>=2$ and $u$ is a $C^2$ function
on $Omega$.
#hide[
  @simon_lectures_2022
  @gilbarg_elliptic_2001
  @han_elliptic_2011
  @yu_lecture_2021
]

= Mean value and maximal value principle

#definition[
  $u in C^2(Omega)$ is called *harmonic* if $laplace u=0$ in $Omega$, is called 
  sub/super-harmonic if $laplace u>=0$ / $laplace u<=0$ in $Omega$
]

#theorem(name: "Mean Value Property")[
  For a harmonic $u$, we have $
    u(x)#text(blue)[=]1/(op("Vol")(B(x,R)))Int(B(x,R),,)u(y)dd(y)
  $ where $op("Vol")(B(x,R))$ can be written as $omega_n R^n$
]
#proof[
  Let $F(R)=1/(omega_n R^n)int_(B(x_0,R))u(x)dd(x)$, $r=abs(x-x_0)$, we have  $
    F(R)&=1/(omega_n R^n)Int(B(x_0,R),,)u(x)abs(nabla r)^2 dd(x) \
    &=1/(omega_n R^n)(Int(diff B(x_0,R),,)r u(x)dd(sigma)
    -Int(B(x_0,R),,)u r laplace r dd(x)-Int(B(x_0,R),,)u_r dd(x))
  $ Since $u$ is harmonic, $
    0&#text(blue)[=]Int(B(x_0,R),,)laplace u(x)dd(x)=Int(diff B(x_0,R),,)u_r dd(sigma)
  $ This also shows that $
    Int(B(x_0,R),,)u_r dd(x)=Int(0,R)Int(diff B(x_0,R),,)u_r dd(sigma)dd(r)
    #text(red)[=]0
  $ Hence $
    F(R)&#text(blue)[=]1/(omega_n R^n)(dv(,R)(omega_n R^(n-1) F(R))
    -Int(B(x_0,R),,)u r (n-1)/r dd(x)) \
      &=1/(R^(n-1))dv(,R)(R^n F(R))-(n-1)F(R)
  $ #ie $
    F'(R)#text(red)[=]0
  $ 
]
#remark[
  If $u$ is sub/super-harmonic, replace $#text(blue)[=]$ with $>=$/$<=$,
  $#text(red)[=]$ with $<=$/$>=$, the theorem still holds.
]

Using mean-value property, we can prove a series of important properties.

#theorem(name: "Strong Maximum Principle")[
  If $u$ is sub-harmonic, then $u$ cannot attain a maximum in $Omega$ unless
  $u$ is constant.
]
#proof[
  Suppose $u$ attains maximum $M$ at some $x_0 in Omega$, mean-value property
  shows that $u equiv M$ in a neighborhood of $x_0$. Easy to see the set
  ${u=M}$ is both open and closed. Hence $u$ is constant.
]

#corollary[
  - If $u$ is sub-harmonic, continuous to $diff Omega$, then $u$ must attain its
    maximum on $diff Omega$.
  - If $u,v$ are both harmonic with same boundary value, then $u equiv v$.
]

#corollary[
  If $laplace u>=f$ for some continuous $f$ then we have the following estimates: $
    u(x_0)&<= 1/(omega_n R^n)Int(B(x_0,R),,)u+C R^2 sup_(B(x_0,R)) f_- \
    sup_Omega u&<=sup_(diff Omega)u+C d^2 sup_Omega f_-
  $ where $C$ depend only on $n$, $d=op("diam")Omega$, $f_-=max{-f,0}$
]
#proof[
  Wlog assume $x_0=0$. Note $laplace (r^2)=2n$, so $
    laplace(u+r^2/(2n)sup_Omega f_-)=f+sup_Omega f_- >=0
  $ Apply mean-value principle and maximum principle, we get the desired
  inequalities. \
]

= Green's function & Elliptic regularity

By divergence theorem, $
  Int(Omega,,)v laplace u dd(x)+Int(Omega,,)nabla u dot.c nabla v=Int(diff Omega,,)
  v nabla_nu u dd(sigma) 
$ Interchange $u,v$ and subtract we get $
  Int(Omega,,)(v laplace u-u laplace v) dd(x)=Int(diff Omega,,)
  v nabla_nu u-u nabla_nu v dd(sigma) #h(2em)"(Green's identity)"
$ Let $Gamma(x)$ be the fundamental solution of $laplace$, #ie $laplace Gamma=delta_0$.
Let $v_y(x)=Gamma(y-x)$, we get  $
  u(y)=Int(Omega,,)Gamma(y-x) laplace u+Int(diff Omega,,)u nabla_nu (Gamma(y-x))
  -Gamma(y-x)nabla_nu u dd(sigma).
$ We remark that $
  Gamma(x)=cases(
    1/(2 pi) log abs(x)\,#h(2em) & n=2,
    -1/(n(n-2)omega_n)dot.c 1/(abs(x)^(n-2))\, & n>=3
  )
$ Now suppose that there is a harmonic $h in C^1 paren.l macron(Omega)paren.r
sect C^2(Omega)$, again by green's identity we have $
  0=Int(Omega,,)h laplace u+Int(diff Omega,,) u nabla_nu h-h nabla_nu u dd(sigma).
$ Let $G(x,y)=Gamma(x,y)+h(x)$, for choose $h=h_y$ such that $G=0$ on $diff Omega$,
then we have more generally $
  u(y)=Int(Omega,,)G(x,y)laplace u(x)dd(x)+Int(diff Omega,,)u nabla_nu G(x,y)
  dd(sigma(x)).
$ This $G$ is called the *Green function* of $laplace$ w.r.t region $Omega$.

For $Omega=B(x,R)$ with $u$ harmonic on $bar(Omega)$, we can choose  $
  G(x,y)=cases(
    Gamma(y-x)-Gamma(abs(y)/R (y'-x))\, #h(2em) & y!=0,
    Gamma(x)-Gamma(R)\, & y=0
  )
$ where $y'=R^2/(abs(y)^2) y$

Direct calculation shows that when $abs(x)=R$, $
  nabla_nu G=G_r (x,y)=(R^2-abs(y)^2)/(n omega_n R)dot.c 1/abs(y-x)^n.
$ Note $
  pdv(abs(y-x), r)=(r^2-x dot.c y)/(r abs(y-x))
  #h(1em)"and"#h(1em) abs(x-y')/abs(x-y)=R/abs(y).
$ Here $r=abs(x)$.

This gives the Poisson integral formula: $
  u(y)=(R^2-abs(y)^2)/(n omega_n R)Int(diff B(0,R),,) u(x)/abs(y-x)^n dd(sigma(x))
$ 
#remark[
  This shows that a harmonic $u in C^2$ is always smooth.
]
Easy to verify that for any $vphi in L^1(diff B(0,R))$, $
  u(y)=(R^2-abs(y)^2)/(n omega_n R)Int(diff B(0,R),,) vphi(x)/abs(y-x)^n dd(sigma(x))
$ is a smooth harmonic function in $B(0,R)$. Moreover if $u(y)->vphi(x)$ as $y->x$
for any continuous point $x in diff Omega$ of $vphi$.

#theorem(name: "Elliptic regularity of Laplacian")[
  Let $u in L_"loc"^1(Omega)$, or more generally, $u in cal(D)'(Omega)$, satisfying
  $laplace u=f in C^oo (Omega)$, then $u$ is smooth in $Omega$.
] <reg>

#lemma[
  Let $f in C_0^oo (RR^n)$, then $
    (Gamma*f)(x)=(Int(RR^n,,)f dd(x)) Gamma(x)+O(abs(x)^(-n+1)) "as" abs(x)->oo
  $ 
] <decay_of_sol>
#proof[
  Suppose $op("supp")f subset B(0,R)$, $n>=3$, denote $abs(x)$ by $r$, then $
    abs((Gamma*f)(x)-(Int(RR^n,,)f dd(x))Gamma(x))
    &=1/(n(n-2)omega_n)abs(Int(RR^n,,)(f(y))/abs(x-y)^(n-2)-(f(y))/abs(x)^(n-2) dd(y)) \
    &<=C sup abs(f) dot.c Int(B(0,R),,)((r+R)^(n-2)-r^(n-2))/(r^(n-2)(r-R)^(n-2))dd(y) \
    &=O(abs(x)^(-n+1)) "as" abs(x)->oo
  $ Proof is similar for $n=2$.
]

#remark[
  We can prove a more general version of @decay_of_sol:
]
#theorem[
  Suppose $f in cal(E)'(RR^n)$ and $u=Gamma*f$, then we have when $abs(x)->oo$, $
    u(x)=pari(f,1) dot.c Gamma(x)+O(abs(x)^(-n+1))\,#h(2em) & n>=3
  $ 
]

#lemma[
  If $u in cal(E)'(RR^n)$ is a compactly supported distribution, $laplace u=f$ for
  some $f in cal(D)'$, then $u$ is uniquely represented by $Gamma * f$, with possible
  exception up to an additive constant when $n=2$. Note that the
  general convolution $*$ is defined $cal(D)'times cal(E)'-> cal(D)'$, and by assumption
  $f$ is also compactly supported.
]
#proof[
  Let $chi_eps$ be a sequence of smooth approximation of $delta_0$, let $u_eps=
  u*chi_eps$, then $lap u_eps=f*chi_eps=:f_eps$. Note $u_eps$ and $f_eps$ are compactly
  supported and smooth.
  Easy to check $
    lap (Gamma*f_eps)=(lap Gamma)*f_eps=f_eps.
  $ Let $v_eps=u_eps-Gamma*f_eps$, then $v_eps$ is smooth and harmonic. Note that
  $Gamma*f_eps=O(log abs(x))$, and $u_eps$ is compactly supported, so by @liouville,
  $v_eps$ is constant. For $n>=3$, by @decay_of_sol, $v_eps=O(1/abs(x))->0$ as
  $abs(x)->oo$, hence $v_eps=0$ and $u_eps=Gamma*f_eps$. Let $eps->0$, we see
  $u=Gamma*f$. For $n=2$, we have $v_eps-C(eps) log r=O(1/r)$. But $v_eps$ is a constant,
  hence we must have $C(eps)=0$ and $v_eps equiv 0$.
]

#proof(name: [of @reg])[\ #h(2em)
  We prove more generally, if $lap u=g in cal(D)'(RR^n)$, then $u$ is smooth where $g$
  is smooth. More precisely, for any $B(x,2R) subset Omega$ such that
  $g$ is smooth on $B(x,2R)$, choose a smooth bump $eta$ that is $1$ on $B(x,R)$ and
  supported on $B(x,2R)$. We have $eta u in cal(E)'$ and $
    lap (eta u)=(lap eta)u+2 nabla eta dot.c nabla u+eta lap u
    =(lap eta)u+2 nabla eta dot.c nabla u+eta g=:U+eta g
  $ Note that the both sides supported on $B(x,2R)$, extend everything to $RR^n$ by 0,
  we have $
    eta u=Gamma * U+Gamma*(eta g)
  $ Since $eta g in C_0^oo$, $Gamma*(eta g)$ is smooth on $RR^n$.
  Note that $U$ is zero in $B(0,R)$, so for $y in B(x,R)$, the convolution of $Gamma$
  does not involve the value of $Gamma$ around 0, hence $eta u$ is smooth around $x$.
  So is $u$.
]

Next, we turn to the existence of solutions.

#theorem[
  For any $f in C^oo (Omega)$, there exists a smooth $u$ #st $lap u=f$.
]
#proof[
  Let $chi(r)$ support on $r<=2$ and equal to $1$ for $r<=1$, $vphi_k (x)=chi(abs(x)-k)$.
  Let $u_k==Gamma*(vphi_k f)$ satisfying $lap u_k=vphi_k f$, then let $v_k=u_(k+1)-u_k$.
  We want to find harmonic functions $h_k$ such that $sum_k (v_k+h_k)$ converges
  uniformly on every compact set.

  Note that $v_k$ is harmonic on $B(0,k)$, hence by @analytic, analytic. We can choose a
  part sum of its Taylor expansion $P_k$ such that $
    sup_(B(0,k\/2)) abs(v_k-P_k)<=1/2^k
  $ Note that $P_k$ is necessarily a harmonic polynomial. Let $h_k=-P_k$, and $
    u=u_1+sum_(k>=1)(v_k-P_k).
  $ Easy to check $lap u=f$ in $cal(D)'$ sense. By @reg, $u$ is smooth.
]
#remark[
  We may now involve @reg in the last step. By using gradient estimates, we can see the
  convergent is $C^k$ for any $k$, on every compact set.
]


#proof(name: [Another approach of @reg])[\ #h(2em)
First assume $f=0$, #ie, $u$ is a harmonic distribution. Let $chi(x)=chi(abs(x))$ be
  our favorite cut-off function and $chi_eps->delta_0$. Then for any $eps>0$,
  $u_eps=u*chi_eps$ is a smooth harmonic function. So by mean value property, $
    u_eps*chi_delta=u_eps,#h(1em) forall delta>0
  $ since $chi_delta$ is a radical function. But by property of convolution, $
    u_eps*chi_delta=u*chi_eps*chi_delta=u*chi_delta*chi_eps=u_delta
  $ Hence $u_eps$ is independent of $eps$. Let $eps->0$, we see $u$ is a smooth harmonic
  function.

  For general $f$, by last theorem there is a smooth $v$ such that $lap v=f$.
  Then $u-v$ is harmonic and smooth. Hence $u$ is smooth.
]

= Harnack's inequality & Gradient estimate

#theorem(name: "Harnack's Inequality")[
  If $u$ is non-negative harmonic function, then for any compact $K subset Omega$,
  there is a constant $C=C(K)>0$ such that $
    sup_K u <= C inf_K u
  $ 
] <harnack>
#proof[
  Directly followed by Poisson integral formula, we have for $y in B(x,R) subset
  Omega$, $
    (1-r/R)/(1+r/R)^(n-1)<=u(y)/u(x)<= (1+r/R)/(1-r/R)^(n-1)
  $ where $r=abs(x-y)$. Note $u(x)!=0$ because otherwise $u equiv 0$.
] Now choose a finite open cover $B(x_j,r_j)$ of $K$ #st $B(x_j,4r_j) subset Omega$,
any $x,y$ can be written as a sequence $x=z_0,z_1,...,z_k=y$ such that
$z_(i-1),z_i in B_(j_i)$, then $
  u(y)/u(x)<=product_i (1+r_i/R_i)/(1-r_i/R_i)^(n-1)<=((1+2/3)/(1-2/3)^(n-1))^(C(k))
$ where $r_i=abs(z_(i-1)-z_i)$, $R_i=3r_(j_i)$.

#theorem[
  Let $u$ be harmonic on $Omega$, $B(x_0,R) subset subset Omega$, then $
    abs(nabla u(x_0))=1/(omega_n R^n) abs(Int(B(x_0,R),,) nabla u dd(x))
    =1/(omega_n R^n)abs(Int(diff B(x_0,R),,)u nabla r dd(sigma))
    <= n/R sup_(diff B(x_0,R)) abs(u).
  $ Further, we have $
    abs(u(x_0))=1/(omega_n R^n)abs(Int(B(x_0,R),,)u(x)dd(x))<=1/(omega_n R^n)Int(B(x_0,R),,)abs(u)dd(x)
  $ Hence we can improve the result as $
    abs(nd u(x_0))<= (2n)/R sup_(pt B(x_0,R\/2))abs(u)
    <= n/omega_n (2/R)^(n+1) dot.c Int(B(x_0,R),,)abs(u)dd(x)
  $ 
]
#corollary[
  + Let $d_x=d(x,diff Omega)$, then #h(1fr) $
      abs(nabla u(x))<= n/d_x sup_Omega u
    $ 
  + Let $alpha$ be any multiple index, then $
      sup_(Omega')abs(nabla_alpha u)<= ((n abs(alpha))/d)^abs(alpha) sup_Omega abs(u).
    $ Where $d=d(Omega',diff Omega)$. In particular, $
      norm(nabla u)_(L^oo (B_r)) <= n/(R-r) norm(u)_(L^oo (B_R))
    $ 
] <gradient_est>

We can prove a better result:

For a positive harmonic $u$ and $B(x_0,2R) subset Omega$, $
  abs((nabla u(x_0))/u(x_0))=(1/(omega_n R^n) abs(int_(B(x_0,R)) nabla u dd(x)))/
  (1/(n omega_n R^(n-1))abs(int_(diff B(x_0,R)) u dd(sigma)))
  =n/R abs((int_(diff B(x_0,R))u nabla r dd(sigma))/(int_(diff B(x_0,R))u dd(sigma)))
  <= n/R (sup_(diff B(x_0,R)) u)/(inf_(diff B(x_0,R)) u)
  <= (n e^n)/R
$ 

#corollary[
  Let $u$ be a smooth harmonic function, then $u$ is analytic.
] <analytic>
#proof[
  Suppose $B(x_0,2R)subset subset Omega$, by @gradient_est, we have $
    norm(nabla_alpha u)_(L^oo (B(x_0,R)))<=C (A_1 abs(alpha))^abs(alpha).
  $ Note that $
    n^abs(alpha)=\(underbrace(1+1+dots.c+1,n)\)^abs(alpha)=sum_(abs(beta)<=abs(alpha))
    (abs(beta)!)/(beta!).
  $ In particular, we have $
    abs(alpha)!<=n^abs(alpha)alpha!.
  $ Hence by Stirling's formula, $
    norm(nabla_alpha u)_(L^oo (B(x_0,R)))<=C (A_2)^abs(alpha)alpha!.
  $ Hence the level $k$ term of Taylor expansion is no more than $
    M_k<=C A_2^k dot.c n^k (x-x_0)^k<=C A_3^k abs(x-x_1)^k,#h(1em)
    "uniform for" x_1 in B(x_0,R).
  $ This proves $u$ is analytic in a small neighborhood of $x_0$.
]

#corollary(name: "Liouville theorem")[
  If a harmonic function $u$ on $RR^n$ is bounded, then it is constant.
] <liouville>
#proof[
  Apply gradient estimate to $u$, we have $
    sup_(B(0,R))abs(nabla u)<= n/R sup_(B(0,2R)) abs(u)<= (C n)/R->0 "as" R->oo
  $ Hence $nabla u equiv 0$, and $u$ is a constant.
] 
#remark[
  + Further, we can refine the result to $
    u(x)=O(log abs(x))==>u(x)="constant"
  $ 
  + Using the same method we can prove if a harmonic function has polynomial growth,
  then it is a polynomial.
]

On the other hand, we can prove these results by estimate $lap abs(nabla u)^2$ and
$laplace abs(nabla log u)^2$.

#proof[
  + We have $
    1/2 lap abs(nd u)^2&=abs(nd^2 u)^2+pari(nd u,nd lap u)=abs(nd^2 u)^2 \
    1/2 lap abs(u)^2&=abs(nd u)^2+u lap u =abs(nd u)^2
  $ Then for a smooth bump $eta$ that is $1$ in $B(x_0,R\/2)$ and supported in $B(x_0,R)
  cc cc Omega$, $
    1/2 lap(eta^2 abs(nd u)^2)&=1/2 lap (eta^2)abs(nd u)^2
    +4eta pari(nd eta tens nd u, nd^2 u)+eta^2 abs(nd^2 u)^2 \
    &=(1/2 lap (eta^2)-4abs(nd eta)^2)abs(nd u)^2
    +(2abs(nd eta)abs(nd u)-eta abs(nd^2 u))^2 \
    &>=-C abs(nd u)^2
  $ Hence $lap(eta^2 abs(nd u)^2+a abs(u)^2)>=0$. Apply maximum principle, we see $
    sup_(B(x_0,R\/2)) abs(nd u)<=C' sup_(B(x_0,R)) abs(u)
  $

  + Let $v=log u$, $w=abs(nabla v)^2$, note $laplace v=-abs(nabla v)^2$, $
    1/2 laplace w&=abs(nabla^2 v)^2+pari(laplace nabla v, nabla v)
    =abs(nabla^2 v)^2-pari(nabla abs(nabla v)^2,nabla v) \
    &=abs(nd^2 v)^2-pari(nd w,nd v)
  $ Note that $
    abs(nd^2 v)^2&>=1/n (lap v)^2=1/n abs(nd v)^4=w^2/n \
    abs(nd w)^2&=4abs(nd v dot.c nd^2 v)^2<=4 abs(nd v)^2 abs(nd^2 v)^2
  $ Then $
    &#hide[=]1/2 lap(eta^2 w)+pari(nd(eta^2 w),nd v) \
    &=1/2 lap (eta^2)w+2eta pari(nd eta,nd w)+eta^2 abs(nd^2 v)^2-w pari(nd(eta^2),nd v) \
    &>=1/2 lap(eta^2) abs(nd v)^2-2eta abs(nd eta) abs(nd v) abs(nd^2 v)
    -2eta abs(nd eta)abs(nd v)^3+eta^2 abs(nd^2 v)^2 \
    &>=eta^2/(2n) abs(nd v)^4+1/2 lap(eta^2)abs(nd v)^2
    -2eta abs(nd eta)abs(nd v)^3-2abs(nd eta)^2abs(nd v)^2 \
    &=(eta^2)/(2n)abs(nd v)^4-2eta abs(nd eta)abs(nd v)^3
    +(eta lap eta-abs(nd eta)^2)abs(nd v)^2 \
    &>=eta^2/(4n)w^2-C
  $ Suppose $eta^2 w$ attains maximum at $x_0 in B(x_0,R)$. Then we have $
    0>=1/2 lap (eta^2 w)(x_0)+pari(underbrace(nd(eta^2 w),=0 "at" x_0),nd v)
    >=eta^2/(4n)w(x_0)^2-C
  $ Hence $
    sup_(B(x_0,R\/2))w<=sup_(B(x_0,R))eta w<=C'
  $ #ie $
    sup_(B(x_0,R\/2))abs(nd log u)<=C''
  $
] <harnack_alt>

_Reference to @han_elliptic_2011, lemma 1.31, 1.32._

= Convergence arguments
#theorem[
  A continuous function $u$ is harmonic if and only if on every disk, $u$ satisfy
  the mean value property.
]
#proof[
  Fix a ball $B(x_0,R) subset subset Omega$, there exists a harmonic $v$ in $B$ that
  agrees with $u$ on $diff Omega$, then $u-v$ satisfy mean value property for any ball
  contained in $B$ and $u-v=0$ on $diff B$. Then $u-v$ satisfy maximum principle and
  hence identically 0.
]

Apply this theorem we immediately get
#theorem[
  Uniform limit of harmonic functions is harmonic.
]

Actually any limit of harmonic functions is harmonic, since the equation $lap u=0$
is preserved by distribution limit (the weakest limit). This implies that, for example, 
let $cal(H)$ be space of harmonic functions. Then $cal(H) sect L^p$ is a closed subspace
for any $p in [1,oo]$.

#theorem[
  Let $u_k$ be a monotone increasing sequence of harmonic functions on $Omega$ and
  there exists $x_0 in Omega$, such that $u_k (x_0)$ is bounded. Then there is a harmonic
  $u$ such that $u_k->u$ uniformly on any compact $K subset Omega$.
]
#proof[
  Apply Harnack inequality to $u_j-u_i, j>i>=N$.
]
#remark[
  We see by gradient estimate that $u_k -> u$ in $C^m$ for any $m$ on compact $K$.
]
By the same reason, we have:
#theorem[
  Every bounded closed subset of $cal(H) sect L^oo (Omega)$ is compact, in the sense of
  uniform convergence on every compact subset.
]

= Living on manifolds
Replace $nabla$ by covariant derivative and $lap$ by $lap_g$, we can generalize the
results of harmonic functions to Riemannian manifolds.

Let $u$ be a $C^2$ harmonic function on $(M,g)$, the mean value property does not holds
in general if $B(x,R)$ is replaced by geodesic balls, but maximum principle remains true,
as well as its corollaries.

For simplicity, we assume $M$ is compact in the following of this section.

#theorem(name: "Maximum principle on manifolds")[\ #h(2em)
  Let $u in C^2(Omega) sect C^0(bar(Omega)\)$ is sub-harmonic, $Omega cc M$
  if $u$ attains its maximum at $x_0 in Omega$, then $u$ is necessarily a constant.
]
For the proof, we need a lemma:
#lemma[
  Let $u in C^2(Omega)sect C^0\(bar(Omega)),Omega cc M$, satisfying $lap_g u>0$.
  Then $u$ attains maximum on $pt Omega$.
]
#proof[
  Suppose $x_0 in Omega$ and $u(x_0)=sup_Omega u>sup_(pt Omega) u$. Choose geodesic
  normal coordinate around $x_0$, then we have $nd u(x_0)=0$ and $lap u(x_0)<=0$.
  But $lap_g u(x_0)=lap u(x_0)$. This contradicts to $lap_g u>0$
]
#proof(name: "of maximum principle")[\ #h(2em)
  Let $M=sup_Omega u$, $K={x in Omega:u(x)=M}$ closed. Suppose $K subset.neq Omega$,
  Choose a ball $B(x_0,R)cc Omega$ such that $B(x_0,R)sect K={x_1}$. We can do this by
  choose a maximal ball centered at some point close to $K$ and then choose an inner
  tangent ball to a boundary point in $K$. Using normal coordinate around $x_0$,
  let $r=d(x,x_0)$, $R=d(x_0,x_1)$. Define $
    u_eps=u+eps (e^(a(R^2-r^2))-1)=u+eps w
  $ Fix a small $delta$. Note that on $bar(B)(x_0,R)sect pt B(x_1,delta)$, $u<M-c$ for
  some $c>0$ since $u<M$ on $bar(B)(x_0,R)\\{x_1}$. Then $
    lap u_eps&=lap u+2eps a(2a r^2-(1+r lap r)) e^(a(R^2-r^2)) \
    &>=2eps a(2a r^2-n-(n-1)k r) e^(a(R^2-r^2))
  $ where $Ric_g>=-(n-1)k^2$. We can choose a large $a$ such that
  $lap u_eps>0$ on $B(x_1,2delta)$. Then choose $eps$ small enough such that $u_eps<M$
  on $pt B(x_1,delta)$. We can do this since $
    cases(
      w(x)>0\, "in" B(x_0,R),
      w(x)=0\, "on" pt B(x_0,R),
      w(x)<0\, "out of" bar(B)(x_0,R)
    )
  $ Now, since $u_eps (x_1)=u(x_1)=M$. This contradicts to the lemma, applied to $u_eps$
  on $B(x_1,delta)$.
]

Unfortunately, Green's function cannot be written down explicitly on general Riemannian
manifolds. But we can still prove its existence. One may not express a solution of
$lap_g u=f$ by a integral of its boundary value, but the existence and uniqueness of the
solution remains true. _Reference to @aubin_nonlinear_1982, chapter 4_.

The elliptic regularity still holds but need more complicated techniques, which is easier
to prove for $u$ in $H^1(M)$ using bootstrap techniques. We remark further that for
harmonic maps between manifolds, there exists example that is $H^1$ but not continuous.
Nevertheless, continuous harmonic maps are always smooth. One can show this by localize
the coordinate on target and use similar bootstrap methods.

What are still elementary to prove are Harnack inequality and gradient estimates.

#theorem[
  Let $(M,g)$ be a Riemannian manifold with $Ric_g>=-(n-1)K$, $K>0$. Let $u$ be a
  positive harmonic function on $B(x_0,R)$, then there exists $C=C(n)$ #st $
    sup_(B_(R\/ 2))abs(nabla u)/u <= C (1+sqrt(K) R)/R
  $ 
]
#proof[
  Copy calculation in alternative proof of @harnack, let $v=log u$, $w=abs(nd v)^2$.
  Let $chi(t)$ be our favorite cut-off function that is $1$ for $t<=1$ and supported on
  $t<=2$, let $eta(x)=chi((2r)/R)$
  then $
    &#hide[=]1/2 lap(eta^4 w)+pari(nd(eta^4 w),nd v) \
    &=(eta^4)/(2n)abs(nd v)^4-4eta^3 abs(nd eta)abs(nd v)^3
    +2eta^2(eta lap eta-abs(nd eta)^2)abs(nd v)^2+eta^4 Ric(nd v,nd v) \
    &=eta^4/(2n)abs(nd v)^4-(8eta^3)/R chi'((2r)/R)abs(nd v)^3+eta^4 Ric(nd v,nd v) \
    &#hide[=]+((4eta^3)/R chi'((2r)/R)lap r+(8eta^3)/R^2 chi''((2r)/R)
    -(8eta^2)/R^2 chi'((2r)/R)^2)abs(nd v)^2 \
    &>=eta^4/(2n)abs(nd v)^4-(c_1 eta^3)/R abs(nd v)^3-(c_2 eta^2)/R^2 abs(nd v)^2
    -(c_3 eta^3)/R (1+sqrt(K)R)/R abs(nd v)^2-c_4 K abs(nd v)^2 \
    &>=eta^4/(4n)abs(nd v)^4-c_5 eta^2 ((1+sqrt(K)R)/R)^2 abs(nd v)^2 \
    &>=eta^4/(8n)abs(nd v)^4-c_6((1+sqrt(K)R)/R)^4
  $ where we used $chi'<=0$, $lap r<= (n-1)/r (1+sqrt(K)r)$ and $chi'=0$ for $t<=1$.
  Apply maximum principle, we get $
    sup_(B(x_0,R\/2)) abs(nd u)/u=sup_(B(x_0,R\/2))abs(nd v)<=C (1+sqrt(K)R)/R
  $ 
] 

For compact manifolds, we have nice characterization for $lap$ operator. #ie
#theorem[
  Let $(M,g)$ be a compact Riemannian manifold. Then for any $f in C^oo (M)$, $
    lap u=f
  $ has a smooth solution $u$ if and only if $int_M f=0$. The solution is unique up to
  an additive constant.
]
#proof[
  Left after Sobolev spaces.
]

= Monotonicity formula
For harmonic functions, we have the monotonicity formula on domain side.
#theorem[
  Let $u$ be a smooth function on $(M,g)$, define $
    E(R)=1/2 Int(B(0,R),,)abs(nabla u)^2 dd(V_g)
  $ Then $
    dv(,R) E(R) =& (n-2)/R E(R)+Int(diff B(0,R),,)abs(u_r)^2 dd(V_(tilde(g)))
    -1/R Int(B(0,R),,)r u_r lap_g u dd(V_g) \
    &+ 1/(2R) Int(B(0,R),,)(r pdv(,r) log sqrt(det g)) dot.c abs(nabla u)^2 dd(V_g) \
    &+ 1/R Int(B(0,R),,) abs(u_theta)^2 dd(V_g)
    + 1/R Int(B(0,R),,)r II^(diff B(0,r)) (u_theta, u_theta) dd(V_g)
  $ where $u_theta$ is the projection vector of $nd u$ onto $T pt B(0,R)$.
]
#proof[
  Choose geodesic normal coordinate on $B(0,R)$, we use $dd(x),dd(V_g)$ for the Euclidean
  volume element and Riemannian volume element respectively. And denote by $dd(sigma)$ and
  $dd(sigma_g)$ the Euclidean and Riemannian volume element on $pt B(0,R)$ respectively.
  We have $
    dd(V_g)=sqrt(det g)dd(x),quad
    dd(sigma_g)=sqrt(det tilde(g))dd(sigma)=sqrt(det g)dd(sigma).
  $ The metric is
  written as $
    g=dd(r)^2+tilde(g)_(alpha beta)dd(theta^alpha)dd(theta^beta)
  $  $
    dv(,R)E(R)&=1/2dv(,R)Int(B(0,R),,)abs(nd u)^2sqrt(det g)dd(x)
    =1/2Int(pt B(0,R),,)abs(nd u)^2sqrt(det g)dd(sigma) \
    &=1/2 Int(pt B(0,R),,)abs(nd u)^2 dd(sigma_g)
    =1/2 Int(pt B(0,R),,)pari((r nd r)/R abs(nd u)^2,(r nd r)/R)dd(sigma_g) \
    &"Note" (r nd r)/R=nu "is the outer normal of" pt B(0,R) \
    &=1/(2R)Int(B(0,R),,)div_g (r nd r abs(nd u)^2) dd(V_g) \
    &=1/(2R)Int(B(0,R),,)div_g (r nd r) abs(nd u)^2 dd(V_g)
    +1/R Int(B(0,R),,)pari(r nd r tens nd u, nd^2 u) dd(V_g) \
    &=:I_1+I_2
  $ To calculate $I_1$, note $
    div_g (r nd r)=tr_g nd (r nd r)=abs(nd r)^2+r lap r=1+r lap r
  $ On the other hand, $
    div_g (arrow(x))&=1/sqrt(det g) pdv(,x^i)(x^i sqrt(det g))
    =n+x^i pdv(,x^i)log sqrt(det g) \
    &=n+r pdv(,r)log sqrt(det g)
  $ Hence $
    lap r=(n-1)/r+pdv(,r)log sqrt(det g)
  $ When we have a Ricci bound for $M$, say $Ric>=-(n-1)K, K>0$, then this term is
  estimated by $
    lap r<=(n-1) (1+sqrt(K)r)/r
  $ For $I_2$, $
    pari(r nd r tens nd u, nd^2 u)&=g^(j k)x^i nd_k u nd_i nd_j u \
    &=g^(j k)nd_j (x^i nd_i u dot.c nd_k u)-g^(j k)nd_j x^i nd_i u nd_k u
    -g^(j k)x^i nd_i u nd_j nd_k u \
    &=div_g (r u_r nd u)-pari(nd (r nd r), nd u tens nd u)-r u_r lap u \
    &=div_g (r u_r nd u)-abs(u_r)^2-r Hess r(nd u, nd u)-r u_r lap u
  $ Hence $
    dv(,R)E(R)&=1/(2R)Int(B(0,R),,)n abs(nd u)^2
    +(r pdv(,r)log sqrt(det g))dot.c abs(nd u)^2 dd(V_g) \
    &#hide[=]#text(orange)[$+1/R Int(pt B(0,R),,) r u_r nd_nu u dd(sigma_g)$] \
    &#hide[=]-1/R Int(B(0,R),,)abs(u_r)^2+r Hess r(nd u, nd u)+r u_r lap u dd(V_g) \
    &=(n-2)/R E(R)#text(orange)[$+Int(pt B(0,R),,)abs(u_r)^2dd(sigma_g)$]
    -1/R Int(B(0,R),,)r u_r lap u dd(V_g) \
    &#hide[=]+ 1/(2R) Int(B(0,R),,)(r pdv(,r)log sqrt(det g))dot.c abs(nd u)^2 dd(V_g) \
    &#hide[=]+ 1/R Int(B(0,R),,)abs(nd u)^2-abs(u_r)^2 dd(V_g)
    -1/R Int(B(0,R),,)r Hess r(nd u,nd u)dd(V_g)(nd u,nd u)dd(V_g)
  $ Let $(xi^1,...,x^n)=(r,theta^1,...,theta^(n-1))$, we have $
    nd^2_(i,j)r=pdv(r,xi^i,xi^j)-Gamma_(i j)^k pdv(r,xi^k)=-Gamma_(i j)^1
  $ since $pdv(r,r)=1, pdv(r, theta^i)=0$. If we denote by $rho$ the index of $r$
  coordinate, $alpha,beta=1,...,n-1$, then $
    Hess r=-Gamma_(alpha beta)^rho dd(theta^alpha)dd(theta^beta)
    -2Gamma_(alpha rho)^rho dd(r)dd(theta^alpha)-Gamma_(rho rho)^rho dd(r)^2
  $ Easy calculation shows $
    Gamma_(rho rho)^rho=0,quad Gamma_(alpha rho)^rho=Gamma(rho alpha)^rho=0 \
    Gamma_(alpha beta)^rho=-1/2 pdv(tilde(g)_(alpha beta),r)
  $ On the other hand, the 2nd fundamental form of $pt B(0,r)into B(0,r)$ is $
    II=h_(alpha beta)dd(theta^alpha)dd(theta^beta)
    =pari(nd_(pdv(,theta^alpha))pdv(,theta^beta),pdv(,r))dd(theta^alpha)dd(theta^beta)
    =Gamma_(alpha beta)^rho dd(theta^alpha)dd(theta^beta)
  $ Hence $
    Hess r(X,Y)=-II(X^(parallel),Y^(parallel))
  $ where $X^parallel$ is the projection of $X$ onto $T pt B(0,r)$.
  For $u$, note $
    nd u=u_r dd(r)+pdv(u,theta^alpha)dd(theta^alpha)=u_r dd(r)+u_theta
  $ Hence $abs(nd u)^2=abs(u_r)^2+abs(u_theta)^2$. Plug this in, we get $
    dv(,R) E(R) =& (n-2)/R E(R)+Int(diff B(0,R),,)abs(u_r)^2 dd(V_(tilde(g)))
    #text(red)[$-1/R Int(B(0,R),,)r u_r lap_g u dd(V_g)$] \
    &+ 1/(2R) Int(B(0,R),,)(r pdv(,r) log sqrt(det g)) dot.c abs(nabla u)^2 dd(V_g) \
    &+ 1/R Int(B(0,R),,) abs(u_theta)^2 dd(V_g)
    + 1/R Int(B(0,R),,)r II^(diff B(0,r)) (u_theta, u_theta) dd(V_g)
  $ as desired.
]
#remark[
  If $u$ is harmonic, the red term is 0.

  For harmonic map $u#h(-.02em):M->N$, we can embed $N$ into some $RR^k$ by isometry.
  Then we can view $u$ as a vector function on $M$. We have $lap_g u perp T N$, so $
    u_r dot.c lap_g u=0
  $ and the red term is still 0.
]

#ignore[
As a corollary, we prove the volume comparison theorem:
#proposition[
  Let $(M,g)$ be a Riemannian manifold, such that $Ric_g>=(n-1)K$. Let $V_K (R)$ be the
  volume of geodesic ball in space form of constant curvature $K$, then $
    dv(,R)(V(R))/(V_K (R))<=0
  $ 
]
#proof[
  Let $u=r$ in monotonicity formula, then $
    2E(R)=op("Vol")(B(0,R))=:V(R)
  $ We have $
    dv(,R)V(R)&=(n-2)/R V(R)+2op("Vol")(pt B(0,R)) \
    &#hide[=]-2/R Int(B(0,R),,)r lap r dd(V_g)+1/R Int(B(0,R),,)r(lap r-(n-1)/r)dd(V_g)
  $ Note that $op("Vol")(pt B(0,R))=dv(,R)V(R)$, we get $
    dv(,R) V(R)-n/R V(R)=1/R Int(B(0,R),,)r (lap r-(n-1)/r)dd(V_g)
  $ 
] ]

Next, we calculate the monotonicity formula of the frequency function.
#lemma[
  Let $u$ be a smooth function on $(M,g)$, let $
    I(R)=1/2 Int(pt B(0,R),,)abs(u)^2dd(V_g)
  $ Then using the same method as in the proof of last theorem, we have $
    dv(,R)I(R)&=1/2dv(,R)Int(pt B(0,R),,)abs(u)^2 abs(nd r)^2 dd(sigma_g)
    =1/2 dv(,R)Int(pt B(0,R),,)pari(abs(u)^2 nd r, nu) dd(sigma_g) \
    &=1/2dv(,R)Int(B(0,R),,) div_g (nd r abs(u)^2) dd(V_g) \
    &=1/2dv(,R)Int(B(0,R),,)r lap_g r abs(u)^2+2r u u_r dd(V_g) \
    &=(n-1)/R I(R)+1/2 Int(pt B(0,R),,)(lap_g r-(n-1)/r)abs(u)^2dd(sigma_g)
    +1/2 Int(pt B(0,R),,) nd_nu abs(u)^2 dd(sigma_g) \
    &=(n-1)/R I(R)+Int(B(0,R),,)lap_g abs(u)^2
    +1/2Int(pt B(0,R),,)(pdv(,r)log sqrt(det g)) abs(u)^2 dd(sigma_g) \
    &=(n-1)/R I(R)+2E(R)#text(red)[$+2Int(B(0,R),,)u lap_g u dd(V_g)$] \
    &#hide[$=(n-1)/R I(R)+2E(R)$]
    +1/2Int(pt B(0,R),,)(pdv(,r)log sqrt(det g)) abs(u)^2 dd(sigma_g)
  $ 
]
#theorem[
  Let $
    F(R)=(R E(R))/I(R).
  $ We calculate $dv(,R)log F(R)$.
]
#let ini = math.integral
#let inb = math.attach(math.integral, tr: math.prime)
#proof[
  For simplicity, we use $int=int_(B(0,R))dd(V_g)$, $int'=int_(pt B(0,R))dd(sigma_g)$,
  then $
    dv(,R)log F(R)&=(E'(R))/E(R)-(I'(R))/I(R)+1/R \
    &=1/E inb abs(u_r)^2-1/(R E)ini r u_r lap_g u
    +1/(2R E)ini (r pdv(,r)log sqrt(det g))abs(nd u)^2 \
    &#hide[=]+1/(R E)ini abs(u_theta)^2+1/(R E)ini r II(u_theta,u_theta) \
    &#hide[=]-(2E)/I-2/I ini u lap_g u-1/(2I)inb (pdv(,r)log sqrt(det g))abs(u)^2 \
    &=1/E inb abs(u_r)^2-1/I inb pdv(,r)abs(u)^2-1/(R E)ini r u_r lap_g u
    +1/(R E)ini r II(u_theta,u_theta) \
    &#hide[=]+1/(2R E)ini (r pdv(,r)log sqrt(det g))abs(nd u)^2
    -1/(2I)inb (pdv(,r)log sqrt(det g))abs(u)^2
  $ Now suppose $lap_g u=0$, we have $
    dv(,R)log F(R)
    &=1/E inb abs(u_r)^2-1/I inb pdv(,r)abs(u)^2+1/(R E)ini r II(u_theta,u_theta) \
    &#hide[=]+1/(2R E)ini (r pdv(,r)log sqrt(det g))abs(nd u)^2
    -1/(2I)inb (pdv(,r)log sqrt(det g))abs(u)^2
  $ Note that $
    1/E inb abs(u_r)^2-1/I inb pdv(,r)abs(u)^2
    =1/(I E)(inb abs(u_r)^2 inb abs(u)^2-2inb u u_r)>=0
  $ Hence $
    dv(,R)log F(R)&>=1/(R E)ini r II(u_theta,u_theta)
    +1/(2R E)ini (r pdv(,r)log sqrt(det g))abs(nd u)^2 \
    &#hide[=]-1/(2I)inb (pdv(,r)log sqrt(det g))abs(u)^2
  $ Locally, we can assume $-k^2<=K_Sigma<=K^2$, then $
    -(n-1)K<=lap_g r-(n-1)/r<=(n-1)k,quad r <= pi/(2K)
  $ Then $
    dv(,R)log F(R)&>=1/(R E)ini r II(u_theta,u_theta)
    -((n-1)K)/(2R E)ini r abs(nd u)^2-((n-1)k)/(2I)inb abs(u)^2 \
    &>=1/(R E)ini 2 k r cosh(k r)/sinh(k r)abs(u_theta)^2-(n-1)(k+K) \
    &>=4/R-(n+3)k-(n-1)K 
  $ We can essentially get that in a small neighborhood, $
    dv(,R)log((R e^(c R)E(R))/I(R))>=0
  $ 
]

#pagebreak()
#bibliography("HarmonicFunctions.bib", title: "References")
