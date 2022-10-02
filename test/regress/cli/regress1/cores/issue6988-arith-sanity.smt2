; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ANIA)
(declare-const x Bool)
(set-option :produce-unsat-cores true)
(declare-fun i () Int)
(declare-fun i5 () Int)
(declare-fun i8 () Int)
(assert (or x (< i5 0)))
(push)
(assert (and (= i8 1) (= i5 (+ 1 i)) (= i8 (+ 1 i))))
(push)
(check-sat)
(pop)
(pop)
(assert (= i8 (* i8 3 (+ i8 1))))
(check-sat)
