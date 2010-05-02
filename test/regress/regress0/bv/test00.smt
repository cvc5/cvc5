(benchmark umulov1bw016.smt
:source {
We verify the correctness of an unsigned multiplication
overflow detection unit, which is described in
"Combined Unsigned and Two's Complement Saturating Multipliers"
by M. Schulte et al.

Bit-width: 4

Contributed by Robert Brummayer (robert.brummayer@gmail.com).
}
:status unsat
:category { industrial }
:logic QF_BV
:difficulty { 0 }
:extrafuns ((v1 BitVec[4]))
:extrafuns ((v2 BitVec[4]))
:formula
(let (?e3 bv0[4])
(let (?e4 (concat ?e3 v1))
(let (?e5 (concat ?e3 v2))
(let (?e6 (bvmul ?e4 ?e5))
(let (?e7 (extract[7:4] ?e6))
(let (?e8 (ite (= ?e7 ?e3) bv1[1] bv0[1]))

(let (?e32 (extract[3:3] v2))
(let (?e34 (extract[2:2] v2))
(let (?e35 (bvand (bvnot ?e32) (bvnot ?e34)))
(let (?e36 (extract[1:1] v2))
(let (?e37 (bvand ?e35 (bvnot ?e36)))
(let (?e38 (extract[1:1] v1))

(let (?e39 (bvand ?e38 ?e32))
(let (?e40 (extract[2:2] v1))
(let (?e41 (bvand ?e40 (bvnot ?e35)))
(let (?e42 (bvand (bvnot ?e39) (bvnot ?e41)))
(let (?e43 (extract[3:3] v1))
(let (?e44 (bvand ?e43 (bvnot ?e37)))
(let (?e45 (bvand ?e42 (bvnot ?e44)))

(let (?e82 bv0[1])
(let (?e83 (concat ?e82 v1))
(let (?e84 (concat ?e82 v2))
(let (?e85 (bvmul ?e83 ?e84))
(let (?e86 (extract[4:4] ?e85))
(let (?e87 (bvand ?e45 (bvnot ?e86)))
(let (?e88 (ite (= (bvnot ?e8) (bvnot ?e87)) bv1[1] bv0[1]))
(not (= (bvnot ?e88) bv0[1]))
)))))))))))))))))))))))))))
