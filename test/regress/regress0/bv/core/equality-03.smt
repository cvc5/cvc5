(benchmark B_
  :source {
Source unknown
}
  :status unknown
  :difficulty { unknown }
  :category { unknown }
  :logic QF_BV
  :extrafuns ((x0 BitVec[32]))
  :extrafuns ((x1 BitVec[32]))
  :extrafuns ((x2 BitVec[32]))
  :extrafuns ((y0 BitVec[32]))
  :extrafuns ((y1 BitVec[32]))
  :extrafuns ((y2 BitVec[32]))
  :extrafuns ((a0 BitVec[32]))
  :extrafuns ((a1 BitVec[32]))
  :extrafuns ((a2 BitVec[32]))
  :extrafuns ((a3 BitVec[32]))
  :assumption
(xor (and (= a0 x0) (= x0 a1)) (and (= a0 y0) (= y0 a1)))
  :assumption
(xor (and (= a1 x1) (= x1 a2)) (and (= a1 y1) (= y1 a2)))
  :assumption
(xor (and (= a2 x2) (= x2 a3)) (and (= a2 y2) (= y2 a3)))
  :formula
(not (= a0 a3))
)
