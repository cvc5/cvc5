; COMMAND-LINE: --produce-proofs --proof-granularity=dsl-rewrite --dump-proofs --proof-format-mode=alethe --dag-thres=0
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-fun x () (_ BitVec 25))
(assert (not (= (bvand x (bvshl x (int2bv 26))) (bvxor x x))))
(check-sat)
(exit)
