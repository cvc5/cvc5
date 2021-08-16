; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(set-option :fmf-bound true)
(declare-datatype N ((o) (f) (s)))
(declare-datatype P ((P)))
(declare-fun G (N P Int) Bool)
(declare-datatype c ((c (_p P))))
(declare-fun g (N Int Int) c)
(assert (forall ((x N)) (not (G x P 0))))
(assert (forall ((t Int)) (or (< t 0) (> t 1) (and (forall ((p P)) (or (exists ((y N)) (and (G y (_p (g y 0 0)) t)))))))))
(check-sat)
