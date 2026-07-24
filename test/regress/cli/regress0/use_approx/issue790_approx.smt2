; REQUIRES: glpk
; COMMAND-LINE: --use-approx
; EXPECT: sat
(set-logic QF_LIA)
(set-info :source "Reduced from regression 'assert-fail-arith-production.smt2' using ddSMT to exercise GLPK. Originally, the input was derived from a scrambling of 20-vars/cut_lemma_01_006.smt2. See https://github.com/cvc5/cvc5/issues/790")
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun x () Int)
(declare-fun x6 () Int)
(declare-fun x4 () Int)
(assert (and (= 0 (+ x6 1 (* 2 x4))) (= 0 (+ (* x 51725) (* x6 241)))))
(check-sat)
