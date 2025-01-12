#import "@phyxmeow/preamble:0.1.0": *
#show: preamble.with(
  font: "concrete",
  numbering: "1.1.",
)

= Geometry
#theorem[
  Let $G$ be a locally compact Lie group with at most countably many connect
  components, $X$ a locally compact Hausdorff space. Suppose $G acts X$
  continuously, then for $x in X$ such that $G dot.c x$ is closed, $
    G\/G_x->G dot.c x
  $ is a homeomorphism, where $G dot.c x$ is equipped with the subspace topology.
  If further $M$ is a manifold and the action is smooth, $G dot.c x$ will be
  a embedded submanifold and the map above is smooth. (Note that in this case,
  the quotient $G->G dot.c x$ will be a smooth submersion and $G_x$ is a
  properly embedded Lie subgroup).
]
#proposition[
  Let $M$ be a complete Riemannian manifold and $alpha:RR->M$ be a complete
  geodesic. Suppose $Im alpha$ is compact, then $alpha$ is closed.
]
#proof[
  $alpha$ can be uniquely lift to a path on the sphere bundle $S(T M)$ by $
    tilde(alpha)(s)=(alpha(s),alpha'(s))
  . $ It is actually the integral curve of $
    X_(x,v)=v^k pdv(,x^k)+Gamma_(i j)^k v^i v^j pdv(,v^k)
  $ on $T M$. $X$ generates Lie group action of $RR acts T M\\ M$. We can
  conclude the result by theorem above. Or by the following argument:

  Suppose $alpha$ is not closed, #ie $tilde(alpha)$ is non-periodic. Then there
  is ${s_k}->oo$ such that $tilde(alpha)(s_k)->p$. But $Im tilde(alpha)$ is
  compact (by the compactness of unit sphere), so $p=tilde(alpha)(s_0)$. Hence
  $tilde(alpha)(s_0)$ is a limit point of $Im tilde(alpha)$. Since $RR$ acts
  transitively on $Im tilde(alpha)$, $Im tilde(alpha)$ is a perfect set.
  Choose a small codim 1 submanifold $W$ through $p$ that is transverse to $X$.
  Then $Im tilde(alpha)$ can only hit $W$ countably many times while $W sect
  Im tilde(alpha)$ is a perfect set. Contradiction.
]
