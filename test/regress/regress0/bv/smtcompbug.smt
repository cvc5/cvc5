(benchmark B_
  :status sat
  :category { unknown }
  :logic QF_BV
  :extrafuns ((x781 BitVec[32]))
  :extrafuns ((x803 BitVec[8]))
  :extrafuns ((x804 BitVec[8]))
  :extrafuns ((x791 BitVec[8]))
  :formula (and
(= x804 (bvxor (bvxor (extract[7:0] (bvadd bv1[32] x781)) x791) x803))
(= (bvnot (extract[0:0] x804)) bv0[1])
(= x781 bv0[32]))
)
