;; Originally a seg fault cause by a zero width vector, fixed by SymFPU 1.2.0

(set-info :smt-lib-version 2.6)
(set-logic QF_BVFP)
(set-info :source |https://github.com/cvc5/cvc5/issues/9697|)
(set-option :produce-models true)
(set-option :check-models true)
(set-info :status sat)

(declare-const c5 (_ BitVec 1))
(declare-const c35 (_ FloatingPoint 8 24))
(declare-const c72 RoundingMode)
(assert (not (= c5 ((_ fp.to_sbv 1) c72 c35))))
(check-sat)
