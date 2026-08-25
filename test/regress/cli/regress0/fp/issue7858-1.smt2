;; An issue with the rounder in SymFPU not handling some exotic formats
;; Fixed in SymFPU 1.2.0
; COMMAND-LINE: --fp-exp
(set-info :smt-lib-version 2.6)
(set-logic QF_FP)
(set-info :source |https://github.com/cvc5/cvc5/issues/7858|)
(set-option :produce-models true)
(set-option :check-models true)
(set-info :status sat)

(declare-fun v () Float64)
(assert (= ((_ to_fp 9 53) RNE v) (fp (_ bv0 1) (_ bv0 9) (_ bv0 52))))
(check-sat)
