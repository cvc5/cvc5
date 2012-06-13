(benchmark bitvec0.smt
:logic QF_BV
:extrafuns ((t BitVec[32]))
:status unknown
:formula
(let (?n1 (extract[4:0] t))
(let (?n2 (extract[6:2] t))
(flet ($n3 (= ?n1 ?n2))
(let (?n4 (extract[6:6] t))
(let (?n5 (extract[0:0] t))
(flet ($n6 (= ?n4 ?n5))
(let (?n7 (extract[1:1] t))
(let (?n8 (extract[5:5] t))
(flet ($n9 (= ?n7 ?n8))
(flet ($n10 (and $n6 $n9))
(flet ($n11 true)
(flet ($n12 (if_then_else $n3 $n10 $n11))
(flet ($n13 (not $n12))
$n13
))))))))))))))
