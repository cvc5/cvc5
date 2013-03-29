(benchmark ext_con_004_004_0016.smt
:logic QF_BV
:extrafuns ((v4 BitVec[16]))
:extrafuns ((dummy4 BitVec[1]))
:extrafuns ((a BitVec[16]))
:status unknown
:formula
(flet ($n1 true)
(let (?n2 (extract[15:13] a))
(let (?n3 (extract[15:14] v4))
(let (?n4 (concat ?n3 dummy4))
(flet ($n5 (= ?n2 ?n4))
(let (?n6 (extract[14:12] a))
(let (?n7 (extract[13:12] v4))
(let (?n8 (concat dummy4 ?n7))
(flet ($n9 (= ?n6 ?n8))
(flet ($n10 (and $n5 $n9))
(let (?n11 (extract[14:14] v4))
(let (?n12 (extract[13:13] v4))
(flet ($n13 (= ?n11 ?n12))
(flet ($n14 (not $n13))
(flet ($n15 (and $n1 $n1 $n1 $n10 $n14))
$n15
))))))))))))))))
