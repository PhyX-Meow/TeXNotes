#import "@phyxmeow/preamble:1.0.0": *
#show: preamble.with(
  font: "concrete",
  numbering: "1.1.",
)

#align(center)[#text(20pt)[
  *Notes of Siu-Yau*
]#v(0.5cm)]

= The idea

The goal of the paper is to prove the following #emph[Frankel conjecture]:
#theorem(name: "Siu-Yau")[
  Every compact Kähler manifold of positive bisectional curvature is bi-holomorphic
  to the complex projective space.
] <main-thm>

To achieve this, we stand on the shoulder of giants:
#theorem(name: "Bishop-Goldberg")[
  The second Betti number of a compact Kähler manifold $M$ of positive bisectional
  curvature is 1.
]
#theorem(name: "Kobayashi-Ochiai")[
  If $M$ is a compact complex manifold with ample line bundle $L$, suppose $
    c_1(M)>=(m+1)c_1(L)
  . $ Then $M$ is bi-holomorphic to $CC PP^n$.
]
