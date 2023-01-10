; REQUIRES: cocoa
; EXPECT: unsat
; COMMAND-LINE: --simplification=none
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_UFFF)
(define-sort FF () (_ FiniteField 17))
(declare-fun f (FF) FF)
(declare-fun d () FF)
(declare-fun e () FF)
(assert (and (=  (ff.add d e)  (ff.mul d e)) (=  (ff.mul d e)  (ff.mul e e)) (not (= (f  (ff.add d e)) (f  (ff.mul e e))))))
(check-sat)

