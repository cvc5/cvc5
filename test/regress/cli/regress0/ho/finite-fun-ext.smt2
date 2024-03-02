; EXPECT: unsat
;; HO not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic HO_ALL)

(declare-datatype Unit ((unit)))

(declare-fun f (Int) Unit)
(declare-fun g (Int) Unit)
(declare-fun P ((-> Int Unit)) Bool)

(assert (P f))
(assert (not (P g)))

(check-sat)
