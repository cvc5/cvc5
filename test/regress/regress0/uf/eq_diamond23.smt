(benchmark eq_diamond23
:source{
Generating minimum transitivity constraints in P-time for deciding Equality Logic,
Ofer Strichman and Mirron Rozanov,
SMT Workshop 2005.

Translator: Leonardo de Moura. }
:status unsat
:category { crafted }
:logic QF_UF
:difficulty { 2 }
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
(x14 U) (y14 U) (z14 U)
(x15 U) (y15 U) (z15 U)
(x16 U) (y16 U) (z16 U)
(x17 U) (y17 U) (z17 U)
(x18 U) (y18 U) (z18 U)
(x19 U) (y19 U) (z19 U)
(x20 U) (y20 U) (z20 U)
(x21 U) (y21 U) (z21 U)
(x22 U) (y22 U) (z22 U)
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
(or (and (= x13 y13) (= y13 x14)) (and (= x13 z13) (= z13 x14)))
(or (and (= x14 y14) (= y14 x15)) (and (= x14 z14) (= z14 x15)))
(or (and (= x15 y15) (= y15 x16)) (and (= x15 z15) (= z15 x16)))
(or (and (= x16 y16) (= y16 x17)) (and (= x16 z16) (= z16 x17)))
(or (and (= x17 y17) (= y17 x18)) (and (= x17 z17) (= z17 x18)))
(or (and (= x18 y18) (= y18 x19)) (and (= x18 z18) (= z18 x19)))
(or (and (= x19 y19) (= y19 x20)) (and (= x19 z19) (= z19 x20)))
(or (and (= x20 y20) (= y20 x21)) (and (= x20 z20) (= z20 x21)))
(or (and (= x21 y21) (= y21 x22)) (and (= x21 z21) (= z21 x22)))
(not (= x0 x22))))
