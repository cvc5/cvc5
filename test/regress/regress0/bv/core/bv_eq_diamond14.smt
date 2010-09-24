(benchmark eq_diamond14
:source{
Generating minimum transitivity constraints in P-time for deciding Equality Logic,
Ofer Strichman and Mirron Rozanov,
SMT Workshop 2005.

Translator: Leonardo de Moura. }
:status unsat
:category { crafted }
:logic QF_BV
:difficulty { 0 }
:extrafuns ((x0 BitVec[32]) (y0 BitVec[32]) (z0 BitVec[32])
(x1 BitVec[32]) (y1 BitVec[32]) (z1 BitVec[32])
(x2 BitVec[32]) (y2 BitVec[32]) (z2 BitVec[32])
(x3 BitVec[32]) (y3 BitVec[32]) (z3 BitVec[32])
(x4 BitVec[32]) (y4 BitVec[32]) (z4 BitVec[32])
(x5 BitVec[32]) (y5 BitVec[32]) (z5 BitVec[32])
(x6 BitVec[32]) (y6 BitVec[32]) (z6 BitVec[32])
(x7 BitVec[32]) (y7 BitVec[32]) (z7 BitVec[32])
(x8 BitVec[32]) (y8 BitVec[32]) (z8 BitVec[32])
(x9 BitVec[32]) (y9 BitVec[32]) (z9 BitVec[32])
(x10 BitVec[32]) (y10 BitVec[32]) (z10 BitVec[32])
(x11 BitVec[32]) (y11 BitVec[32]) (z11 BitVec[32])
(x12 BitVec[32]) (y12 BitVec[32]) (z12 BitVec[32])
(x13 BitVec[32]) (y13 BitVec[32]) (z13 BitVec[32])
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
