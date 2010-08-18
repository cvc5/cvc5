(benchmark eq_diamond14
:source{
Generating minimum transitivity constraints in P-time for deciding Equality Logic,
Ofer Strichman and Mirron Rozanov,
SMT Workshop 2005.

Translator: Leonardo de Moura. }
:status unsat
:category { crafted }
:logic QF_UF
:difficulty { 0 }
:extrafuns ((x0 U) (y0 U) (z0 U)
(x1 U) (y1 U) (z1 U)
(x2 U) (y2 U) (z2 U)
(x3 U) (y3 U) (z3 U)
(x4 U) (y4 U) (z4 U)
(x5 U) (y5 U) (z5 U)
(x6 U) (y6 U) (z6 U)
(x7 U) (y7 U) (z7 U)
(x8 U) (y8 U) (z8 U)
(x9 U) (y9 U) (z9 U)
(x10 U) (y10 U) (z10 U)
(x11 U) (y11 U) (z11 U)
(x12 U) (y12 U) (z12 U)
(x13 U) (y13 U) (z13 U)
)
:formula (and 
(or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1)))
(or (and (= x1 y1) (= y1 x2)) (and (= x1 z1) (= z1 x2)))
(or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3)))
(or (and (= x3 y3) (= y3 x4)) (and (= x3 z3) (= z3 x4)))
(or (and (= x4 y4) (= y4 x5)) (and (= x4 z4) (= z4 x5)))
(or (and (= x5 y5) (= y5 x6)) (and (= x5 z5) (= z5 x6)))
(or (and (= x6 y6) (= y6 x7)) (and (= x6 z6) (= z6 x7)))
(or (and (= x7 y7) (= y7 x8)) (and (= x7 z7) (= z7 x8)))
(or (and (= x8 y8) (= y8 x9)) (and (= x8 z8) (= z8 x9)))
(or (and (= x9 y9) (= y9 x10)) (and (= x9 z9) (= z9 x10)))
(or (and (= x10 y10) (= y10 x11)) (and (= x10 z10) (= z10 x11)))
(or (and (= x11 y11) (= y11 x12)) (and (= x11 z11) (= z11 x12)))
(or (and (= x12 y12) (= y12 x13)) (and (= x12 z12) (= z12 x13)))
(not (= x0 x13))))
