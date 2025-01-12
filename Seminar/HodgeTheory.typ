#import "@phyxmeow/preamble:0.1.0": *
#show: preamble.with(
  font: "concrete",
  numbering: "1.1.",
)

#align(center)[#text(20pt)[
  *Hodge Theory on Manifolds*
]#v(0.5cm)]

#let md = math.upright("d")

= Preliminary

Throughout this note, let $M$ be a compact smooth manifold and $g$ be a Riemannian
metric on $M$. Denote by $Omega^k (M)$ the space of $k$-forms on $M$.
We state several basic fact here:

#definition[
  There is an isomorphism, called the #emph[Hodge star operator] $
    *:Omega^k --> Omega^(n-k)
  $ such that $
    pari(alpha,beta) dd(V_g)=alpha wed * beta 
  $ holds pointwise. Moreover, we have $
    **=(-1)^(k(n-k))Id_(Omega^k)
  $ 
]

#definition[
  There is an formal adjoint operator of $md$, $
    md^*: Omega^k->Omega^(k-1)
  $ such that $
    (dd(alpha),beta)_(L^2)=(alpha,md^*beta)_(L^2)
  $ where $
    (alpha,beta)_(L^2)=Int(M,,)pari(alpha,beta) dd(V_g)
  $ 
]

#proposition[
  + Using the Hodge star operator, we can write #h(1fr) $
      md^*=(-1)^(k(n-k)+k)*d*
    $ 
  + $md^* compose md^*=0$
]

#definition[
  The operator $
    lap=md md^*+md^*md:Omega^k-->Omega^k
  $ is called the #emph[Hodge Laplacian operator].
]

#proposition[
  + $ker md perp img md^*$ and $ker md^* perp img md$. #h(1fr)
  + $lap alpha=0$ if and only if $dd(alpha)=0 "and" md^*alpha=0$ 
  + In local coordinates, suppose $alpha=1/(k!)alpha_(i_1,...,i_k)dd(x^(i_1))wed dots.c
    wed dd(x^(i_k))$, then $
      (dd(alpha))_(i_0,...,i_k)
      &=sum_(s=0)^k (-1)^s pdv(alpha_(i_0,...,hat(i_s),...,i_k),x^(i_s))
      =sum_(s=0)^k (-1)^s nd_(i_s)alpha_(i_0,...,hat(i_s),...,i_k) \
      (md^*alpha)_(i_1,...,i_(k-1))
      &=-g^(p q)pdv(alpha_(p,i_1,...,i_(k-1)),x^q)=-nd^p alpha_(p,i_1,...,i_(k-1)) \
      (lap alpha)_(i_1,...,i_k)&=-g^(p q) pdv(alpha_(i_1,...,i_k),x^p,x^q)
      +"lower order terms" \
    $ 
] <property-dstar>
#proof[
  + Suppose $alpha in ker md$, then #h(1fr) $
      (alpha,md^* beta)=(dd(alpha),beta)=0.
    $ Hence $ker md perp img md^*$. Similarly $ker md^* perp img md$.
  + We have $
      (alpha,lap alpha)=(alpha,md md^* alpha)+(alpha, md^* md alpha)
      =norm(md alpha)^2+norm(md^* alpha)^2 
    $ Hence $lap alpha=0 iff md alpha=0 "and" md^* alpha=0$
  + Direct calculation.
]

The goal of this note is to prove the following theorem:
#theorem[
  There is a orthogonal decomposition $
    Omega^k (M)=cal(H)^k dsum img md dsum img md^*.
  $ Moreover, $cal(H)^k=ker lap$ is finite dimensional.
] <hodge-decomp>

= Facts in Functional Analysis
Let $H$ be a Hilbert space, an unbounded operator $T$ on $H$ is a linear operator
defined on some subspace $D(T)$ of $H$, that may be and may not be bounded.
#definition[
  A unbounded operator is called #emph[densely defined] if $D(T)cc H$ is dense. It is
  called #emph[closed] if the graph $
    Gamma(T)={(v,T v):v in H}cc H times H
  $ is a closed subset. $T$ is called #emph[closable] if there exists a closed operator
  $overline(T)$ such that $Gamma\(overline(T))=overline(Gamma(T))$.
]
#lemma[
  $T$ is closed if and only if for any $v_k$ in $D(T)$, suppose $
    v_k->v,quad T v_k->w
  $ then $v in D(T)$ and $w=T v$. It is closable if and only if for any such sequence,
  $w$ is uniquely determined by $v$.
]
#lemma[
  If $T$ is densely defined and bounded on $D(T)$, then $T$ can be uniquely extended
  to a bounded operator on $H$.
]

#definition[
  For any densely defined operator $T$, we can define the adjoint $T^*$ of $T$.
  First define $
    D(T^*)={u in H:v|->pari(u,T v) "is bounded"}
  $ Then by Riesz representation theorem and the fact $D(T)$ dense, there is a unique
  element $T^* u$ such that $
    pari(u,T v)=(T^*u,v), forall v in D(T).
  $
]
#proposition[
  For any closable $T$ on $H$, we have
  + $D(T^*)$ is closed subspace of $H$.
  + $\(overline(T))^*=T^*$, and $T^*$ is closed.
  + $T^(**)=overline(T)$.
]

#lemma[
  Let $T$ is a densely defined closed operator on Hilbert space $H$, satisfy $
    norm(T v)>=norm(v), forall v in D(T)
  $ Then $T$ is surjective and $T^(-1)$ is a bounded operator with $norm(T^(-1))<=1$.
] <invert>

#theorem[
  Let $T$ be a self-adjoint compact operator on Hilbert space $H$, then
  + All eigenvalues of $T$ are real.
  + Eigenfunctions associated to different eigenvalues are orthogonal.
  + For any $c>0$, $\#{lambda_j:|lambda_j|>c}<oo$, and hence the set of all eigenvalues
    is finite.
  + The eigenspace associated to non-zero eigenvalue is finite dimensional.
  + The normalized eigenfunctions form an orthonormal basis of $H$.
] <spectrum>

= Hodge Decomposition
We introduce the space $cal(A)^k (M)$, which is defined as $
  cal(A)^k (M)={alpha:alpha "be" L^1_"loc""-coefficient" k"-form"
  #st norm(alpha)_(L^2) <oo}
$ Easy to see $cal(A)^k (M)$ is a Hilbert space with dense subspace $Omega^k (M)$.

#lemma[
  $md:cal(A)^k->cal(A)^(k+1)$ and $md^*:cal(A)^k->cal(A)^(k-1)$ are densely defined
  closed operators.
]
#proof[
  Only need to verify for ${alpha_j}cc Omega^k$, if $alpha_j xarrow(L^2)alpha$
  and $dd(alpha_j)("or" md^*alpha_j)xarrow(L^2)beta$, then $beta$ is unique.
  This is obvious in the sense of distributions.
]

#lemma[
  Suppose $alpha in D(lap)$, then $alpha in D(md) sect D(md^*)$.
]
#proof[
  By definition of operator closure, there exists a sequence $alpha_j$ in $Omega^k$
  such that $alpha_j xarrow(L^2) alpha$ and ${lap alpha_j}$ is Cauchy. Then since $
    pari(lap (alpha_i-alpha_j),alpha_i-alpha_j)
    =norm(md(alpha_i-alpha_j))^2+norm(md^*(alpha_i-alpha_j))^2
  $ This shows that both ${md(alpha_i-alpha_j)}$ and ${md^*(alpha_i-alpha_j)}$ are
  $L^2$-Cauchy sequences. Hence $alpha in D(md) sect D(md^*)$. Further we have  $
    norm(lap (alpha_i-alpha_j))^2
    =norm(md md^*(alpha_i-alpha_j))^2+norm(md^*md(alpha_i-alpha_j))^2
  $ This shows that $md alpha in D(md^*)$ and $md^* alpha in D(md)$.
]

#lemma[
  There is a constant $C=C(M,g)>0$ such that for any $alpha in cal(A)^k$, we have  $
    (alpha,lap alpha)+norm(alpha)_(L^2)^2>=C norm(alpha)_(H^1)^2
  $ Where the $H^1$-norm is defined by summation of each derivative of each
  $alpha_(i_1,...,i_k)$.
] <garding>
#proof[
  Using coordinate expansion of $lap alpha$ and integration by parts, we have $
    (alpha,lap alpha)>=norm(alpha)_(dot(H)^1)^2
    -C norm(alpha)_(dot(H)^1)norm(alpha)_(L^2)
  $ Hence $
    (alpha,lap alpha)+C' norm(alpha)_(L^2)^2>=1/2 norm(alpha)_(H^1)^2
  $ Then $
    (alpha, lap alpha)+norm(alpha)_(L^2)^2>=1/(2C') norm(alpha)_(H^1)^2
  $ Note that $(alpha,lap alpha)>=0$.
]

This shows that $1+lap$ is a densely defined closed operator satisfy $
  norm((1+lap)alpha)^2=norm(alpha)^2+2pari(alpha,lap alpha)+norm(lap alpha)^2
  >=norm(alpha)^2
$ Hence by @invert $(1+lap)^(-1)$ is a bounded linear operator.

For a smooth $alpha$, let $alpha->(1+lap)^(-1)alpha$ in @garding, we have $
  norm((1+lap)^(-1)alpha)_(H^1)^2<=1/C (alpha,(1+lap)^(-1)alpha)
  <=1/C norm(alpha)_(L^2)norm((1+lap)^(-1)alpha)_(L^2)
$ Hence $
  norm((1+lap)^(-1)alpha)_(H^1)<=C' norm(alpha)_(L^2)
$ Since $Omega^k$ is dense in $cal(A)^k$, this shows that $img (1+lap)^(-1)cc
cal(A)^k_(H^1)$. By Rellish compact embedding theorem, $(1+lap)^(-1)$ is a compact
operator. By @spectrum, since $(1+lap)^(-1)$ is positive, it has eigenvalues $
  1>=mu_0>=mu_1>=...>0
$ with eigenfunctions $vphi_0,vphi_1,...$ forming a $L^2$-basis of $cal(A)^k$.
Playing with the equation $
  (1+lap)^(-1)vphi_i=mu_i vphi_i
$ we can easily see that $lap$ has eigenvalues $
  0<=lambda_0<=lambda_1<=...
$ with $
  lambda_i=(1-mu_i)/mu_i
$ Hence $ker lap=$ the 1-eigenspace of $(1+lap)^(-1)$, which is finite dimensional.

We define the #text(green)[Green's operator] $G:cal(A)^k->cal(A)^k$ as follows:
For $alpha in cal(A)^k$, write $
  alpha=alpha_0+sum_(j>=1)c_j vphi_j
$ Where $alpha_0$ is the projection of $alpha$ onto $cal(H)=ker lap$, and $vphi_j$
represent all eigenfunctions of positive eigenvalues. Then we define $
  G alpha=sum_(j>=1) c_j/lambda_j vphi_j
$ Denote by $cal(h)$ the projection onto $cal(H)$, then $
  G lap=lap G=1-cal(h)
$ 

Now, we turn to the proof of Hodge theorem.

Using #text(green)[Green's operator], we have $
  alpha=cal(h)alpha+md (md^* G alpha)+md^* (md G alpha)
$ This gives decomposition $
  cal(A)^k=cal(H)_(L^2)^k+img md+img md^*
$ By @property-dstar, note that $
  cal(H)_(L^2)^k=ker md sect ker md^*,quad
  img md cc ker md, quad img md^* cc ker md^*
$ We have $
  cal(H)_(L^2)^k perp img md,quad cal(H)_(L^2)^k perp img md^*,quad
  "and" img md perp img md^*
$ This shows that $
  cal(A)^k=cal(H)_(L^2)^k dsum img md dsum img md^*
$ Note that this also shows that $img md$ and $img md^*$ are closed.

Next, we show that the decomposition is the same for $Omega^k$. We claim $
  overline(md (Omega^(k-1)))=img (md:cal(A)^(k-1)->cal(A)^k)
$ This is because for any $alpha in D(md)$, there exists sequence in $Omega^(k-1)$,
$alpha_j->alpha$ and $md alpha_j-> md alpha$. Then since $img md$ is closed subspace,
the claim is true. Similarly $md^* (Omega^(k+1))$ is dense in $img md^*$.

To finish the proof, we need the elliptic regularity theorem.
#theorem(name: "Local elliptic regularity")[
  Let $
    cal(L)u=-pt_j (a^(i j)pt_i u)+b^i pt_i u+c u
  $ be a elliptic quasi-linear operator Euclidean ball $B(0,2)=:Omega$, suppose
  - $a^(i j),b^i,c in C^oo (Omega)$,
  - $(a^(i j))>=Lambda>0$ uniformly on $Omega$,
  - $cal(L)u=f in C^oo$ in $Omega$ in weak sense.
  Then $u in C^oo (Omega)$.
] <local-regularity>
#lemma(name: "Interior estimate")[
  Under same assumption as the theorem, let $B=B(0,1)$, $B'=\(0,1/2)$. Denote by
  $norm(dot.c)'$ the norm on $B'$, then we have $
    norm(u)'_(H^2)<=C (norm(u)_(L^2)+norm(f)_(L^2))
  $ 
] <interior-est>
#proof[
  First assume $u in C^oo$, choose our favorite bump function $eta$ that is 1 on $B'$
  and supported on $B$, we have $
    Int(B,,) f dot.c (eta^2 u_k)_k=Int(B,,)-(a^(i j)u_i)_j (eta^2 u_k)_k
    +O(C(eta)norm(u)_(H^1) norm(eta u)_(H^2))
  $ By integration by parts, we have $
    Lambda norm(eta nd u_k))_(L^2)^2<=Int(B,,)eta^2 a^(i j)u_(k i) u_(k j)
    <=C(eta)(norm(u)_(H^1)+norm(f)_(L^2))(1+norm(eta u)_(H^2))
  $ Sum over $k$, we have$
    norm(eta u)_(H^2)^2<=C(eta)(norm(u)_(H^1)+norm(f)_(H^2))(1+norm(eta u)_(H^2))
  $ Hence $
    norm(u)_(H^2)^'<=C(eta)(norm(u)_(H^1)+norm(f)_(L^2))
  $ To deal with the term $norm(u)_(H^1)$ on right side, pair with $eta^2 u$ we get $
    Int(B,,)f dot.c eta^2 u>=Int(B,,) eta^2 a^(i j) u_i u_j
    -C(eta) norm(u)_(L^2)^2-C(eta)norm(u)_(L^2) norm(eta u)_(H^1)
  $ From this we can easily get $
    norm(nd u)_(L^2)^'<=C(eta)(norm(u)_(L^2)+norm(f)_(L^2))
  $ Then by choose the ball even smaller in $H^2$-estimates we conclude the result.

  For general $u in H^1$, we may choose $D_k^(-h)(eta^2 D_k^(h)u)$ instead of
  $pt_k (eta^2 pt_k u)$ in $H^2$ estimates, where $D_k^h u=1/h (u(x+h e_k)-u(x))$.
  Then we may get estimates on $D_k^h nd u$, then let $h->0$ we can obtain $u in H^2$.
] #h(1fr)

The local regularity is easily obtained by interior estimate and induction. Now apply
regularity theorem to $alpha in Omega^k$, we have $cal(h)alpha in Omega^k$ since it
is in the kernel of $lap$, then by $
  alpha-cal(h)alpha=lap (G alpha)
$ we get $G alpha in Omega^k$, and so is $md G alpha$ and $md^* G alpha$. And in the
end, we have $
  alpha=cal(h)alpha+md (md^* G alpha)+md^*(md G alpha)
$ decomposes $alpha$ in $Omega^k$, and that $cal(H)^k=cal(H)_(L^2)^k$ is isomorphic to
the $k$-th de Rahm cohomology group.


= Complex Manifolds and Vector Bundles
To be continued...