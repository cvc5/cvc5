; REQUIRES: no-competition
; COMMAND-LINE:
; EXPECT: (error "Parse Error: ./regress0/printer/portfolio-out-err.smt2:7.28: Can only enable use-portfolio via the command line")
; EXPECT: unsat
; DISABLE-TESTER: dump
(set-logic UFLIA)
(set-option :use-portfolio true)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (not (P 10)))
(check-sat)
