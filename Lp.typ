#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  numbering: none,
)

*Lemma.* Let $f:RR->RR$ be a $C^1$-function with bounded derivative and $f(0)=0$.
$u$ be any $W^(1,p)$ function on $RR^n$, then $f compose u$ is $W^(1,p)$ and $
  nd (f compose u)=f'(u) nd u
$ as distributions.

#h(-2em)
_Proof._ Suppose $|f'|<=M$, then we have $|f(x)|<=M|x|$, so  $
  |(f compose u)(x)|<=M|u(x)|
. $ This proves that $f compose u$ is locally integrable and $
  norm(f compose u)_(L^p)<=M norm(u)_(L^p)
. $ Pick $u_k in C_0^oo (RR^n)$ such that $u_k xarrow(W^(1,p))u$. We have $
  |f(u_k (x))-f(u(x))|<=M|u_k (x)-u(x)|
. $ This shows that $f compose u_k xarrow(L^p)f compose u$. Then for any $vphi in
C_0^oo$, we have $
  -pari(f(u_k),nd vphi)=pari(nd(f(u_k)),vphi)=pari(f'(u_k)nd u_k,vphi)
. $ Let $k->oo$, the left hand side is $
  -pari(f(u),nd vphi)=pari(nd (f(u)),vphi)
. $ The right hand side is $
  int_(RR^n)f'(u_k)(nd u_k) vphi dd(x)
. $ Note that $nd u_k xarrow(L^p)nd u$, $f'(u_k)$ is bounded. We can parse to a
subsequence to assume that $u_k->u$ a.e. and $nd u_k->nd u$ a.e. Then $f'(u_k) nd u_k
->f(u)nd u$ a.e. By dominant convergence theorem the integral converges to $
  int_(RR^n)f'(u)(nd u)vphi dd(x)
. $ Hence $
  nd(f(u))=f'(u)nd u
. $ #h(1fr) $square$

#h(-2em)
_Proof of the Proposition._ Let $
  f_eps=sqrt(eps^2+abs(x)^2)-eps,quad v_eps=f_eps compose u
$ Then by lemma we have $
  nd v_eps=u/sqrt(eps^2+abs(u)^2) nd u
. $ We calculate $
  |v_eps-abs(u)|=(2eps abs(u))/(sqrt(eps^2+abs(u)^2)+eps+abs(u))<=max(abs(u),eps)
. $ Hence $v_eps xarrow(L^p)abs(u)$. Also we have $
  abs(u/sqrt(eps^2+abs(u)^2))<=1,quad
  "and" u/sqrt(eps^2+abs(u)^2)-->sign(u) "everywhere"
. $ This shows that $nd v_eps xarrow(L^p)sign(u)nd u$. Since distributions are unique,
we must have $
  nd abs(u)=sign(u)nd u
$ as distributions. Hence $abs(u)in W^(1,p)$.

#h(-2em)
_Another proof for $n=1$._ If $n=1$, we do not need the lemma, in this case
$u in W^(1,p)$ implies $u(x)=int_0^x u(t)dd(t)$ is absolute continuous. Easy to
see by definition that $|u|$ is also AC. Hence it is differentiable a.e. On each of
the sets $
  {u>0},quad {u=0},quad {u<0}
, $ almost every point is a Lebesgue density point. For those $x$ such that $|u|'(x)$
exists and $x$ is a density point of where it lives (for example $A={u>0}$), we can
find a sequence ${x_k}cc A$ such that $x_k->x$. Subtract another null set we can
assume $u'(x)$ also exists. Then $
  |u|'(x)=lim_(k->oo) (|u(x_k)|-|u(x)|)/(x_k-x)=lim_(k->oo) (u(x_k)-u(x))/(x_k-x)
  =u'(x)
. $ Hence $|u|'(x)=u(x)$ a.e. on ${u>0}$. Similarly we can prove $|u|'(x)=0$ a.e.
on ${u=0}$ and $|u|'(x)=-u(x)$ a.e. on ${u<0}$.
