; Logos needs an update for the fix to dt-collapse-updater.
; DISABLE-TESTER: cpc-logos
; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(declare-const x Lst)
(assert (or (not (= ((_ update head) (cons 1 x) 2) (cons 2 x)))
            (not (= ((_ update tail) (cons 1 x) nil) (cons 1 nil)))))
(check-sat)
