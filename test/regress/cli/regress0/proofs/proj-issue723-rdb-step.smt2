; EXPECT: unsat
;; The option below forces the granularity "dsl-rewrite", which leads to an Alethe proof with the operators @bv and @bvsize, where the former is applied to a non-constant argument. This is unsupported.
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x (_ BitVec 1))
(set-option :check-proof-steps true)
(assert (bvult (_ bv0 10) (bvxor ((_ zero_extend 9) x) ((_ zero_extend 9) x))))
(check-sat)
