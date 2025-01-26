#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "",
  numbering: "1.1",
)

= Existence of isothermal coordinates
== Analytic coefficients

#theorem[
  Let $
    dd(s)^2=E dd(x)^2+2F dd(x)dd(y)+G dd(y)^2
  $ be the 1st fundamental form of 
  a surface. Suppose $E,F,G$ are real analytic, then locally there exists isothermal
  coordinates, #emph[i.e.] $
    dd(s)^2=rho (dd(x')^2+dd(y')^2).
  $
]
#proof[
  Using complex coordinate, let $z=x+i y$, then write $
  dd(s)^2=lambda abs(dd(z)+mu dd(macron(z)))^2.
  $ Solve $lambda,mu$ gives $
    lambda=1/4 (E+G+2 sqrt(E G-F^2)),#h(2em) mu=(E-G+2 i F)/(4 lambda).
  $ Then suppose there is another coordinate $w=u(z)+i v(z)$ such that $
    dd(s)^2=e^rho abs(dd(w))^2.
  $ Easy calculation shows $
    dd(s)^2=e^rho abs(w_z)^2 abs(dd(z)+(w_(macron(z)))/(w_z)dd(macron(z)))^2.
  $ Hence we have equation on $w$: $
    w_(macron(z))=mu w_z.
  $ Expand $z$ into $x,y$ gives $
    w_x=i (1+mu)/(1-mu)w_y.
  $ Let $
    U=vec(u,v),#h(2em) a+b i=i (1+mu)/(1-mu).
  $ Then $ 
    pdv(U,x)=mat(a,b;-b,a) pdv(U,y),
  $ where $a,b$ are real analytic functions.

  Then we can apply the Cauchy-Kovalevski theorem to solve $U$. Choose Cauchy data
  to be $
    w(x,0)=x
  $ We expect the solution is a local diffeomorphism, so $U_x,U_y$ should be linearly
  independent. We have $
    U_x=vec(1,0),#h(2em) U_y=mat(a,b;-b,a)^(-1)vec(1,0)=1/(a^2+b^2)vec(a,b)
  $ Calculation shows $b(0,0)!=0$. We are done.
]

== Smooth coefficients
#theorem[
  Same result holds if $E,F,G$ are merely smooth.
]
#proof[
  Choose a non-trivial smooth harmonic function $u$ locally with respect to
  $laplace_g$. $u$ harmonic is equivalent to $dd(star.op dd(u))=0$. So by Poincaré
  lemma there exists locally a smooth $v$ such that $dd(v)=star.op dd(u)$. Note that $
    angle.l dd(u),dd(v) angle.r _g dd(V_g)=dd(u)and star.op dd(v)=0
  $ and $
    angle.l dd(u),dd(u) angle.r _g dd(V_g)=dd(u)and star.op dd(u)=-dd(u)and dd(v)=
    angle.l dd(v), dd(v) angle.r _g dd(V_g)
  $ Hence $dd(u)$ and $dd(v)$ are orthonormal co-frame. #emph[i.e.] $
    g=rho(dd(u)^2+dd(v)^2)
  $
]

== Hölder coefficients
#theorem(name: "Chern")[
  Same result holds if $E,F,G$ are merely $C^(0,alpha),0<alpha<1$.
]
*Reference:* Shing-Shen Chern - An Elementary Proof of the Existence of Isothermal
Parameters on a Surface (1955)
