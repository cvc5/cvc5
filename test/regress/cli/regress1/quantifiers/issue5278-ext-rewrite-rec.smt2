; COMMAND-LINE: --fmf-fun --ext-rewrite-quant -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((a 0)) (((b) (c))))
(define-funs-rec ((d ((x a)) Bool)) ((is-b x)))
(check-sat)
