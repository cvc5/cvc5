; COMMAND-LINE: --seq-array=eager
; DISABLE-TESTER: unsat-core
; timeout with unsat cores
(set-logic QF_SLIA)
(set-info :status unsat)

(declare-fun A () (Seq Int))
(declare-fun B () (Seq Int))
(declare-const x Int)

(assert (= B (seq.rev A)))
(assert (and (<= 0 x) (< x (seq.len A))))
(assert (not (= (seq.nth A x) (seq.nth B (- (- (seq.len A) 1) x)))))

(check-sat)
