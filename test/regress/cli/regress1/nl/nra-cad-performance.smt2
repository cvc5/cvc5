; Source: NRA/keymaera/ETCS-essentials-live-range2.proof-node1388.smt2
; EXPECT: unsat
; REQUIRES: poly
(set-logic NRA)
(set-info :status unsat)
(declare-fun zuscore1dollarskuscore2 () Real)
(declare-fun b () Real)
(declare-fun Muscore0uscore0dollarmvuscore0 () Real)
(declare-fun A () Real)
(declare-fun puscore0dollarskuscore4 () Real)
(declare-fun ep () Real)
(declare-fun uscorenuscore0dollarskuscore2 () Real)
(declare-fun vuscore1dollarskuscore2 () Real)
(declare-fun vo () Real)
(assert (not (exists ((Muscore0uscore0dollarmvuscore0 Real)) (=> (and (and (and (and (and (and (> uscorenuscore0dollarskuscore2 0) (>= (+ zuscore1dollarskuscore2 (* (* uscorenuscore0dollarskuscore2 ep) vo)) puscore0dollarskuscore4)) (= vuscore1dollarskuscore2 vo)) (> vo 0)) (> ep 0)) (> b 0)) (>= A 0)) (or (>= (- Muscore0uscore0dollarmvuscore0 zuscore1dollarskuscore2) (+ (/ (* vuscore1dollarskuscore2 vuscore1dollarskuscore2) (* 2 b)) (* (+ (/ A b) 1) (+ (* (/ A 2) (* ep ep)) (* ep vuscore1dollarskuscore2))))) (>= (+ (* (/ 1 2) (* 2 zuscore1dollarskuscore2)) (* (* (- uscorenuscore0dollarskuscore2 1) ep) vo)) puscore0dollarskuscore4))))))
(check-sat)
