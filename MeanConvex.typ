#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  heading-font: "miama",
  numbering: "1.1.",
)

#title(font:"miama")[
  Mean Convex Region
]

#let Ind = math.op("Ind")
#let kpa = math.kappa
#let indent = h(0em) + v(0em, weak:true)
#show math.equation: set math.lr(size:12pt)
#show math.chevron.l: set text(size:14pt)
#show math.chevron.r: set text(size:14pt)
#let lr(body,s:100%+0pt) = math.lr($(body)$, size:s)
#let bigl(body,s:100%+0pt) = math.lr(body, size:s)

#proposition[
  There does not exists $Omega$ an region in $RR^(n+1)$ with (smooth) boundaries $Sigma_1$ and $Sigma_2$,
  where the mean curvature $H_1>=c>0$ and $H_2>=0$, both pointing inwards.
]

#align(center)[(All the asymptotic notations below is respect to $R->oo$).]

Denote by $g_0$ the Euclidean metric and the induced metric on submanifolds. Let $g=e^(2f)g_0$ where 
$f=-log u$ and $u=R^2-abs(x)^2$. Suppose $Sigma$ is some hypersurface, $e_0,e_1,...,e_n$ is an Euclidean
orthonormal basis where $e_0$ is normal to $Sigma$, then:

- The sectional curvature of $RR^(n+1)$ under $g$ is #h(1fr) $
   tilde(R)(tilde(e)_i,tilde(e)_j,tilde(e)_j,tilde(e)_i)
   &=e^(-2f) dot.c (2g_(i j)T_(i j)-T_(i i)-T_(j j)) \
   &"where" quad T_(i j)=nd_i nd_j f-nd_i f nd_j f+1/2 abs(nd f)^2 g_(i j)
  . $ 
- The covariant derivative becomes $tilde(nd)_X Y=nd_X Y+(nd_X f)Y+(nd_Y f)X-(X dot.c Y)nd f$.
- The mean curvature vector of $Sigma$ becomes $
  tilde(H)_Sigma&=sum_(i=1)^n tilde(nd)_(tilde(e)_i) tilde(e)_i=u sum_i (tilde(nd)_(e_i) (u e_i))^perp
  =u^2 sum_i (tilde(nd)_(e_i) e_i)^perp\
  &=u^2 sum_i (nd_(e_i)e_i+2(nd_i f)e_i-nd f)^perp \
  &=u^2 dot.c (H_Sigma-nd f)^perp
  . $ And the mean curvature is $
    abs(tilde(H)_Sigma)_g=tilde(e)_0 dot.c_g tilde(H)_Sigma=u abs((H_Sigma-nd f)^perp)
  . $ 

#indent

There exists a shortest geodesic from $Sigma_1$ to $Sigma_2$ under $g$, denoted by $gamma:p->q$. Let $T$ be
the Euclidean unit tangent of $gamma$, $gamma'=u T$ be the $g$-unit tangent. Then the equation of $gamma$ is $
  0=tilde(nd)_(gamma')gamma'&=nd_(gamma')gamma'+2(nd_(gamma') f)gamma'-abs(gamma')^2nd f \
  &=u dot.c (nd_T T-(nd_T u)T+nd u) \
  &=(kpa+nd_N u)u N+u dot.c (nd u-(nd_T u)T-(nd_N u)N)
. $ Hence the Euclidean curvature of $gamma$ satisfy $kpa=-nd_N u$. Take a $g$-unit length
normal parallel variation field $X$ along $gamma$, we have $
  I(X,X)=gamma'(q)dot.c_g tilde(nd)_X X-gamma'(p)dot.c_g tilde(nd)_X X
  +int_gamma abs((underbrace(tilde(nd)_(gamma')X,=0))^perp)^2-tilde(R)(X,gamma',gamma',X)dd(tilde(s))
. $ We have $
  T_(i j)=nd_i nd_j f-nd_i f nd_j f+1/2 abs(nd f)^2 g_(i j)
  =-1/u nd_i nd_j u+1/(2u^2)abs(nd u)^2 g_(i j)
, $
  and the curvature $
  tilde(R)(tilde(e)_i,tilde(e)_j,tilde(e)_j,tilde(e)_i)=cases(
    0\, & quad i=j\,,
    (u_(i i)+u_(j j))u-abs(nd u)^2\, & quad i!=j.
  )
$ Taking trace for $X(p)in T_p Sigma_1$ we get $
  tr I&=u T(q)dot.c_g tilde(H)_2-u T(p)dot.c_g tilde(H)_1
  -int_gamma tr_X tilde(R)(X,gamma',gamma',X) dd(tilde(s)) \
  &=u T(q)dot.c (H_2-n nd f)-u T(p)dot.c (H_1-n nd f)-int_gamma dots.c \
  &=-u(p)abs(H_1(p))-u(q)abs(H_2(q))-n(u T(q)dot.c nd f-u T(p)dot.c nd f)-int_gamma dots.c
. $ Here $
  u T(q)dot.c nd f-u T(p)dot.c nd f&=int_gamma hat(nd)_T (u nd_T f) dd(s) \
  &=-int_gamma hat(nd)_T nd_T u dd(s)=-int_gamma hat(nd)_T (nd u dot.c T)dd(s) \
  &=-int_gamma nd^2_(T,T)u+nd u dot.c kpa N \
  &=int_gamma -u_(T T)+abs(u_N)^2
. $ Then $
  tr I&=-u(p)abs(H_1(p))-u(q)abs(H_2(q))-int_gamma (lap u-u_(T T))u-n u abs(u_N)^2
  -n abs(nd u)^2dd(tilde(s)) \
  &<=-u(p)abs(H_1(p))+int_gamma n abs(nd u)^2-(lap u-u_(T T))u dd(tilde(s))
. $ Now let $u=(R^2-abs(x)^2)^2$, then  $
  nd u&=-4(R^2-abs(x)^2)x \
  u_(i i)&=-4(R^2-abs(x)^2)+8x_i^2
. $ We have $
  n abs(nd u)^2-(lap u-u_(T T))u&=(16n abs(x)^2+4n R^2-4n abs(x)^2-8abs(x)^2+8(x dot.c T)^2)u \
  &<=16n R^2 u
  . $ Then $
  tr I<=-u(p)c+16n R^2 int_gamma u dd(tilde(s))
. $ Fix $p_0 in Sigma_1,q_0in Sigma_2$ such that segment $ov(p_0q_0)cc Omega$. Then $
  tilde(L)(ov(p_0q_0))=O(R^(-4))
  . $ Note that $u<=R^4$, so $u(p)<=C R^2$. Hence $
  a:=R-abs(p)=sqrt(u(p))/(R+abs(p))=O(1)
  . $ Then $u=O(a^2 R^2)$ for points close to $p$, and we have estimate $
  abs(gamma(t)-p)<=int_0^t u dd(tilde(s))=O(a^2 R^(-2)) quad "for all" t
. $ Finally, we have $
  tr I<=-c a^2(2R-a)^2+C a^2<0 quad "for large" R
. $ Hence $gamma$ is unstable, this is a #underline[contradiction].

#remark[
  If $R$ is fixed, say $R=1$. And assume both surface have $H>=c>0$, then the above arguments could
  give $c<="constant"$, where the constant is around 16. I'm thinking how to improve it to 2.
]
