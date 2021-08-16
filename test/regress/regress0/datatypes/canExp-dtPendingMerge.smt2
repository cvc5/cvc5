; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((T 0)) (((A) (B (proj0B T) (proj1B T)) (C (proj0C T)) (D (proj0D T) ))))
(declare-fun w () T)
(declare-fun u () T)
(assert (= w (B (D u) (B (D u) (C w)))))
(check-sat)
