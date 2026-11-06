; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: (a)
; EXPECT: sat
(set-option :produce-unsat-assumptions true)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const c Bool)
(declare-const d Bool)
(declare-const a Bool)
; nested if-then-else terms lifted out of an equality and an inequality whose
; other argument is a variable or constant
(assert (= x (ite c (ite d (+ y 1) 0) y)))
(assert (>= 3 (ite d x y)))
(assert (=> a (> y 5)))
(check-sat)
(check-sat-assuming (a))
(get-unsat-assumptions)
(check-sat-assuming ((not a)))
