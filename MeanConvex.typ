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

- The sectional curvature of $RR^(n+1)$ under $g$ is $tilde(R)_(i j j i)=-(2R^2)/(R^2-abs(x)^2)^4<0$.
- The mean curvature of $Sigma$ becomes $tilde(H)_Sigma=e^(-f)(H_Sigma-n nd f)^perp$.
- The covariant derivative becomes $tilde(nd)_X Y=nd_X Y+(nd_X f)Y+(nd_Y f)X-(X dot.c Y)nd f$.

#text(gray)[
So we have $
  abs(tilde(H)_Sigma)=(R^2-abs(x)^2)(abs(H_Sigma)pm (2n pari(x,e_0))/(R^2-abs(x)^2))
  >=(R^2-abs(x)^2)abs(H_Sigma)-2n abs(x)
. $ If $H_Sigma>=c>0$, then for $R$ sufficiently large and $|x|<R_0:=R-R^(-1)-n\/c=R-O(1)$, we have
$tilde(H)_Sigma>=H_Sigma$.

#underline[Suppose] both $|p|,|q|<R_1=R_0-n\/c$, let $gamma'$ be the $g$-unit tangent of $gamma$, denote
$H_(Sigma_i)$ by $H_i$, then by the mean-convex assumption, $ 
  gamma'(p) dot.c tilde(H)_1-gamma'(q) dot.c tilde(H)_2
  &>=(R^2-abs(p)^2)abs(H_1)-2n abs(p)-2n abs(q) \
  &>=(R^2-R_1^2)abs(H_1)-4n R_1 \
  &>=abs(H_1)>0 quad quad "(for" R "large)".
$
] #indent

Fix a $eps>0$. If $d:=inf_(x in Sigma_1,y in Sigma_2) abs(x-y)<eps$, there exists a pair of points in $Sigma_1$
and $Sigma_2$ with distance at most $eps$. If $d>eps$, note that for any $|v|<d$, $Sigma_1 sect (Sigma_2+v)=OO$.
Pick $p_0 in Sigma_1$, $q_0 in Sigma_2$ with $abs(p_0-q_0)<d+eps/2$, let $v=(d-eps/2)(p_0-q_0)/abs(p_0-q_0)$,
replace $Sigma_2$ by $Sigma_2+v$. Hence we can assume there are $p_0 in Sigma_1$, $q_0 in Sigma_2$ such that
$abs(p-q)<eps$. Further, we could assume the segment $ov(p_0 q_0)$ lies between $Sigma_1$ and $Sigma_2$, #ie
in $Omega$. Finally, move the origin so that $p_0+q_0=0$. Note that under conformal metric $g$, $
  tilde(d)(p_0,q_0)<=eps/(R^2-|p_0|^2)<=2eps R^(-2) quad "for large" R
. $ #indent

There exists a shortest geodesic from $Sigma_1$ to $Sigma_2$ under $g$, denoted by $gamma:p->q$. Let $T$ be
the Euclidean unit tangent of $gamma$, $gamma'=u T$ be the $g$-unit tangent. Then the equation of $gamma$ is $
  0=tilde(nd)_(gamma')gamma'&=nd_(gamma')gamma'+2(nd_(gamma') f)gamma'-abs(gamma')^2nd f \
  &=u (nd_T T+2(T dot.c x)T-2x) \
  &=(kpa-2x dot.c N)u N
. $ Hence the Euclidean curvature of $gamma$ satisfy $kpa=2x dot.c N$. Take a $g$-unit length
normal parallel variation field $X$ along $gamma$, we have $
  I(X,X)=gamma'(q)dot.c_g tilde(nd)_X X-gamma'(p)dot.c_g tilde(nd)_X X
  +int_gamma abs((underbrace(tilde(nd)_(gamma')X,=0))^perp)^2-tilde(R)(X,gamma',gamma',X)dd(tilde(s))
. $ Taking trace for $X(p)in T_p Sigma_1$ we get $
  tr I&=u T(q)dot.c_g tilde(H)_2-u T(p)dot.c_g tilde(H)_1+n int_gamma 2R^2 dd(tilde(s)) \
  &=T(q)dot.c (H_2-n nd f)-T(p)dot.c (H_1-n nd f)+2n R^2 tilde(L)(gamma) \
  &=-abs(H_1(p))-abs(H_2(q))-n(T(q)dot.c nd f-T(p)dot.c nd f)+2n R^2 tilde(L)(gamma)
. $ Here $
  T(q)dot.c nd f-T(p)dot.c nd f&=int_gamma nd_T nd_T f dd(s)=int_gamma nd_T lr( (2x dot.c T)/u ) dd(s) \
  &=int_gamma 2+2kpa (x dot.c N)+(2x dot.c T)^2/u dd(tilde(s)) \
  &=int_gamma 2+(2x dot.c N)^2+(2x dot.c T)^2/u dd(tilde(s)) \
  &>0
. $ Note that $tilde(L)(gamma)<tilde(L)(ov(p_0 q_0))<2eps R^(-2)$, so $
  tr I< -abs(H_1(p))-abs(H_2(q))+2n R^2 tilde(L)(gamma)<=-c+4n eps<0
. $ 

Hence $gamma$ is unstable, this is a #underline[contradiction].

#set text(gray)

So there is at least one of $p,q$ lies $O(1)$ close to ${|x|=R}$. Note that when $|x|=R-O(1)$, $u=R^2-abs(x)^2
=O(R)$, so the conformal factor is $Omega(R^(-1))$. Since $tilde(L)(gamma)$ is $O(R^(-2))$, we see $|p-q|$ is 
$O(R^(-1))$.
#remark[
  Actually this could be upgrade to $O(R^(-k))$ for any integer $k$ by the following:
  Consider a large $R$, we know there is pair of points in $B(0,R\/2)$ with distance $O(R^(-1))$, when
  $R$ gets large this pair will have $g$-distance $O(R^(-3))$. The same argument shows the ends of the shortest
  geodesic in $B(0,R)$ will have distance $O(R^(-2))$. Repeat this we may get $O(R^(-k))$ for any $k$.
]

Now let $a=max(R-|p|,R-|q|)$, Then $a=O(1)$ and around here $u=O(a R)$, similar argument as above gives
$|p-q|=O(a R^(-1))$. (Constant depends only on $n,c$, not $R$ and $a$). Consider the ball $B_1=B(p,2|p-q|)$.
In $B_1$, $
  1/u=1/(2 a R)dot.c (1+O(R^(-1))) quad => quad g=1/(2a R)^2 (g_0+ O(R^(-1)))
, $
