(benchmark fuzzsmt
:logic QF_BV
:status sat
:formula
(let (?n1 bv0[9])
(let (?n2 bv29[5])
(let (?n3 (sign_extend[4] ?n2))
(let (?n4 (bvsmod ?n1 ?n3))
(let (?n5 bv1[9])
(flet ($n6 (bvult ?n4 ?n5))
$n6
)))))))
