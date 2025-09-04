#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "xcharter",
  heading-font: "miama",
  numbering: "1.1.",
)

#title(font:"miama")[
  Notes of Micallef-Moore
]

#let bt = bar(math.partial)
#let Ind = math.op("Ind")
#show math.equation: set math.lr(size:12pt)
#show math.angle.l: set text(size:14pt)
#show math.angle.r: set text(size:14pt)
#let lr(body,s:100%+0pt) = math.lr($(body)$, size:s)
#let bigl(body) = math.lr(body, size:100%+0pt)

= Intro
#v(-9pt)
Let $(M,g)$ be a $n$-dimensional Riemannian manifold, $p in M$. Recall that the curvature can be viewed as 
an operator $
  cal(R):wed^2 T_p M-->wed^2 T_p M,quad
  pari(cal(R)(v wed w),eta wed xi)=pari(R(v,w)xi,eta)
. $ The metric can be extend to a Hermitian metric on $T_p M tens CC$ by $
  pari(v,w)=g(v,bar(w)), quad v,w in T_p M tens CC
. $ The curvature operator is extended $CC$-linearly, we get $
  cal(R):wed^2 T_p M tens CC-->wed^2 T_p M tens CC
. $ To each complex two-plane $sigma=span{v,w}cc T_p M tens CC$, we can assign a complex sectional curvature
to it $
  K_sigma=pari(cal(R)(v wed w),v wed w)/abs(v wed w)^2
. $ $v in T_p tens CC$ is called _isotropic_ if $g(v,v)=0$, a complex subspace $V$ is called _totally isotropic_
if every $v in V$ is isotropic. $(M,g)$ is called have positive isotropic curvature or _PIC_ if $K_sigma>0$
for every totally isotropic 2-plane $sigma$. Note that the dimension of a totally isotropic subspace is at
most $n/2$. The condition is non-vacuous only for $n>=4$.

For an isotropic vector $xi=v+i w$, we have $
  0=g(xi,xi)=abs(v)^2-abs(w)^2-2v dot.c w
. $ Hence $abs(v)=abs(w)$ and $v perp w$. Thus for an totally isotropic 2-plane $sigma$, there is a basis 
${v,w}$ such that there is $e_1,...,e_4$ orthonormal with $
  v=e_1+i e_2,quad w=e_3+i e_4
. $ Then $
  v wed w=(e_1wed e_3-e_2wed e_4)+i(e_1 wed e_4+e_2 wed e_3)
, $ and $
  K_sigma=pari(cal(R)(v wed w),v wed w)=R_(1331)+R_(2442)+R_(1441)+R_(2332)-2R_(1234)
. $ Suppose $M$ is pointwise strictly quarter-pinched, #ie $1/4 Lambda(p)<K_sigma|_p<=Lambda(p)$, Berger's
inequality gives $
  abs(R_(1234))<1/2 Lambda(p)
. $ This implies $M$ is PIC. PIC is also implied by positive curvature operator.

= Index of harmonic 2-spheres
Let $f:Sigma->M$ be a non-constant harmonic map, it's known that $f$ is a branched minimal immersion. $f^* T M$
is a *smooth* vector bundle with pull-back metric, which extends $CC$-linearly to $E=f^* T M tens CC$. We claim 
there is a unique holomorphic structure on $E$ such that $nd''=bt$. We may view $pdv(f,z)$ as a section of 
$f^* T M tens CC$. $f$ is harmonic so $nd_(bt_z) pdv(f,z)=0$, #ie it is a holomorphic section of $E$. The 
energy of $f$ is given by $
  E(f)=1/2 int_Sigma abs(pt_x f)^2+abs(pt_y f)^2 dd(x)wed dd(y)
, $ which is invariant under conformal change of coordinate. The second variation of energy by vector field 
$V$ is given by $
  I(V,V)=int_Sigma abs(nd V)^2-tr_Sigma R_M (nd f,V,V,nd f) dd(x)wed dd(y)
, $ The #emph[index] of $f$ the maximal dimension of subspace of $Gamma(f^* T M)$ where $I(dot.c,dot.c)$ is 
negative definite. $V$ is called #emph[Jacobi field] if $I(dot.c,V)=0$.

Extend the index form to a Hermitian form on $Gamma(E)$, we have
#lemma[
  If $W in Gamma(E)$, then $
    I(W,W)=4 int_Sigma abs(bt_z W)^2-pari(cal(R)(W wed pt_z f),W wed pt_z f)dd(x)wed dd(y)
  . $ 
]
#proof[
   First note that, $
    4int_Sigma abs(bt_z W)^2 dd(x)wed dd(y)&=-4int_Sigma pari(pt_z bt_z W,W)dd(x) wed dd(y) \
    &=-int_Sigma pari((nd_x nd_x +nd_y nd_y)W,W)
    -i pari((nd_x nd_y-nd_y nd_x) W,W)dd(x)wed dd(y) \
    &=int_Sigma abs(nd W)^2-i R (pt_x,pt_y,W,ov(W))dd(x)wed dd(y)
  . $ Hence $
    I(W,W)=int_Sigma 4 abs(bt_z W)^2&+i R(pt_x,pt_y,W,ov(W)) \
    &-R(W,pt_x,pt_x,ov(W))-R(W,pt_y,pt_y,ov(W))dd(x)wed dd(y)
  . $ We have $
    &i R(pt_x,pt_y,W,ov(W))-R(W,pt_x,pt_x,ov(W))-R(W,pt_y,pt_y,ov(W)) \
    &=-i R(W,pt_x,pt_y,ov(W))+i R(W,pt_y,pt_x,ov(W))-R(W,pt_x,pt_x,ov(W)),R(W,pt_y,pt_y,ov(W)) \
    &=-R(W,2pt_z,2bt_z,ov(W)) \
    &=-4pari(cal(R)(W wed pt_z),W wed pt_z)
  . $ #v(-24pt)
]
#lemma[
  When $Sigma=SS^2$, $X$ is a holomorphic vector field on $SS^2$, then $f_* X$ is an isotropic complex Jacobi 
  field.
]
#proof[
  Polarization, we get $
    2Re I(V,f_*X)&=I(V+f_* X,V+f_* X)-I(V,V)-I(f_*X,f_*X) \
    &=4 int_Sigma 2 Re pari(bt_z V,bt_z f_*X)-pari(cal(R)((V+f_*X) wed pt_z),(V+f_*X)wed pt_z) \
    &#hide[=]+pari(cal(R)(V wed pt z),V wed pt_z)+pari(cal(R)(f_*X wed pt z),f_*X wed pt_z) dd(x)wed dd(y)
  . $ Note that $f_*X wed pt_z=f_*(X wed pt_z)=0$ since $X=h pt_z$ for some $h$ holomorphic, and $bt_z X=0$. 
  Hence $Re I(V,f_*X)=0$, and $Im I(V,f_*X)=-Re I(i V,f_*X)=0$.
]
From the lemma we see the dimension of the space of Jacobi fields is at least 6, coming from the holomorphic
and anti-holomorphic vector fields on $SS^2$. 

#theorem[
  Suppose $M$ is PIC, then any non-constant harmonic map $f:SS^2->M$ has index at least $floor(n/2)-1$.
]
#proof[
  By theorem of Grothendieck, $E$ splits into sum of holomorphic line bundles $L_1 dsum dots.c dsum L_n$, and 
  the isomorphic classes are uniquely determined up to permutation. WLOG assume $
    c_1(L_1)>=c_1(L_2)>=dots.c>=c_1(L_n)
  . $ Note that the metric extends to a complex bilinear form, which is preserved by parallel transport. It 
  can be view as a section of $E^*tens E^*$, #ie a isomorphism $E->E^*$. Hence $E iso E^*$, it follows that $
    c_1(L_i)=-c_1(L_(n+1-i))
  . $ If $W_i,W_j$ is meromorphic sections of $L_i,L_j$, suppose $
    g(W_i,W_j):SS^2-->CC^*
  , $ is not identically 0, then #text(red)[WHY?] it must have degree 0, #ie $c_1(L_i)+c_1(L_j)=0$. 
  In other words, $
    c_1(L_i)+c_1(L_j)!=0 => (L_i,L_j)_g=0
  . $ Then we have $
    E=E_0 dsum plus.circle.big_(c_1(L_i)>0) (L_i dsum L_(n+1-i))
  . $ In particular, $E_+=plus.circle.big_(c_1(L_i)>0)L_i$ is an isotropic subbundle of $E$, and $g$ is 
  non-degenerate on $E_0$. Moreover, let $z=x+i y$ be the standard coordinate on $SS^2$, then $pdv(f,z)$
  is a holomorphic section of $E_+$ #text(red)[WHY??] because it vanishes at $oo$ and branch points of $f$.

  By Riemann-Roch, $
    dim_CC {"holo. sections of" L_i}=max{c_1(L_i)+1,0}
  . $ If $W_i$ and $W_j$ are holomorphic sections of $E_0$, then $(W_i,W_j)_g$ is constant. So we can choose 
  a complex orthonormal basis ${W_1,...,W_k}$ of $E_0$. Let $cal(V)$ be the complex linear subspace of 
  $Gamma(E)$ generated by $W_1+i W_2,W_3+i W_4,...$ and $E_+$, which are isotropic. The linear space $
    cal(V)_p={w in E_p:w=W(p) "for some" W in cal(V)}
  $ has dimension at least $floor(n/2)$, including $bigl(pdv(f,z)|)_p$. Thus $cal(V)$ contains a linear 
  subspace $cal(V)_0$ of $dim_CC>=floor(n/2)-1$ such that if $0!=W in cal(V)_0$, then $W wed pt_z f$ is not 
  identically 0. Hence $
    I(W,W)=-4 int_(SS^2)pari(cal(R)(W wed pt_z f),W wed pt_z f) dd(x)wed dd(y)<0
  . $ This shows that $Ind f>=floor(n/2)-1$
]
#remark[
  If $M$ has positive curvature or strictly quarter-pinched sectional curvature, then a modified argument 
  shows $Ind f>=n-2$. We will show any compact simply-connected Riemannian manifold must contain a non-trivial  
  minimal 2-sphere of low index by a min-max argument.
]

= α-critical maps with low index
The idea comes from the following fact:
#proposition[
  Let $f in C^2$ be defined on a compact subset of $RR^n$, then for $v$ in some dense open subset of $RR^n$,
  the map $x|->f(x)+x dot.c v$ has only non-degenerate critical points.
]

Skip for now.

= Harmonic 2-spheres with low index
#theorem[
  If $M$ is a compact Riemannian manifold such that $pi_k (M)!=0$, $k>=2$, then there exists a non-trivial
  harmonic 2-sphere in $M$ of index $<=k-2$.
]
#lemma[
  Let $f:SS^2->M$ be a non-trivial harmonic 2-sphere with $Ind=k$. Given any finite set ${p_i}$ in $M$,
  there is a $k$-dim linear subspace $cal(V)$ of $Gamma (f^* T M)$ such that $I(dot.c,dot.c)$ is negative
  definite and $cal(V)$ vanishes on the neighborhoods of each $p_i$.
]
#proof[
  There is a $k$-dim $cal(V)_0$ with negative definite index form, let $
    cal(S)={X in cal(V)_0:int_(SS^2)abs(V)^2dd(mu_0)=1}
  , $ where $mu_0$ is the standard round metric. Choose $r_0$ small such that $B_i=B(p_i,r_0)$ are disjoint and 
  $d(x,p_i)$ is smooth on $B_i\\{p_i}$. For $0<beta<r_0<1$ let $eta_beta:SS^2->[0,1]$ be $
  eta_beta (x)=cases(
    0 & r_i (x)<beta^2 "for some" i\,,
    (log(beta^2)-log (r_i (x)))/(log beta) quad quad & beta^2<=r_i (x)<=beta "for some" i\,,
    1 & "otherwise".
  ) $ One can verify $
    int_(SS^2) abs(nd eta_beta)^2dd(mu_0)<=C abs(log beta)^(-1)
  . $ Then it follows that $
    int_(SS^2)abs(nd (eta_beta V))^2dd(mu_0)<=(1+delta)int_(SS^2) abs(nd V)^2dd(mu_0)
    +C(1+delta^(-1))abs(log beta)^(-1) sup_(SS^2) abs(V)^2
  . $ For small $delta$ and $beta$, we have $
    I(eta_beta V,eta_beta V)<=(1+eps) I(V,V)+eps sup_(SS^2) abs(V)^2
  , $ for any $eps>0$.
]
#proof(name:"of theorem")[
  According to last section, there is a sequence ${f_alpha}$, critical for $E_alpha$, $alpha->1$, such that 
  the index of $E_alpha$ at $f_alpha$ is $<=k-2$.
]
