; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: (x x)
; SCRUBBER: sed -e 's/a[1-2]/x/g'
(set-option :produce-unsat-assumptions true)
(set-logic QF_LIA)
(declare-const a1 Bool)
(declare-const a2 Bool)
(declare-const x Int)
(assert (= a1 (= x 5)))
(assert (= a2 (not (= x 5))))
(check-sat-assuming (a1 a2))
(get-unsat-assumptions)
