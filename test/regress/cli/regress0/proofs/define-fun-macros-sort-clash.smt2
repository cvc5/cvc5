; DISABLE-TESTER: alethe
; COMMAND-LINE: --parse-define-fun-macros
; EXPECT: unsat
; The name f is used for both a sort and a defined function, which are in
; separate namespaces in SMT-LIB. The defined function is expanded before
; it reaches the solver or proof printer.
(set-logic UFLIA)
(declare-sort f 0)
(declare-fun a () f)
(declare-fun g (f) Int)
(define-fun f ((x f)) Int (+ (g x) 1))
(assert (< (f a) (g a)))
(check-sat)
