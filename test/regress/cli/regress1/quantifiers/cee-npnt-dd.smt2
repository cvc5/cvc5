; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: unsat
;; Unary AND is not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(set-option :fmf-bound true)
(declare-datatype N ((o) (f) (s)))
(declare-datatype P ((p)))
(declare-fun G (N P Int) Bool)
(declare-datatype c ((cc (_p P))))
(declare-fun g (N Int Int) c)
(assert (forall ((x N)) (not (G x p 0))))
(assert (forall ((t Int)) (or (< t 0) (> t 1) (and (forall ((p P)) (or (exists ((y N)) (and (G y (_p (g y 0 0)) t)))))))))
(check-sat)
