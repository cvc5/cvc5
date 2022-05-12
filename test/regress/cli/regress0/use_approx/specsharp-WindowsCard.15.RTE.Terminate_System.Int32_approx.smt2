; REQUIRES: glpk
; DISABLE-TESTER: unsat-core
; COMMAND-LINE: --use-approx
; EXPECT: unsat
(set-logic UFNIA)
(set-info :source "Reduced from regression 'specsharp-WindowsCard.15.RTE.Terminate_System.Int32.smt2' using ddSMT to exercise GLPK")
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun s (Int Int Int) Int)
(declare-fun x (Int Int) Int)
(declare-fun x_ (Int Int) Int)
(assert (and (forall ((? Int)) (! (= (x_ 0 0) (- ? (x_ 0 0))) :pattern ((x ? 1)) :pattern ((x_ 0 0))))))
(assert (and (distinct 0 (s 0 0 0)) (= 0 (x (s 0 0 0) 1))))
(check-sat)
