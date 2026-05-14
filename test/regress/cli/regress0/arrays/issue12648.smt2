; COMMAND-LINE: -i --check-models
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-const a Bool)
(declare-const b (Array Bool (Array Bool Bool)))
(assert (distinct (select b false) (store (select b a) false true) (select b (select (select b a) a)) (select (store b a (select b (select (select b false) (select (select b a) a)))) (select (store (select b false) a (select (select b false) (select (select b false) false))) false))))
(check-sat)
(check-sat-assuming ((= (_ -zero 8 24) (ite (= 1.0 (ite (= (select b false) (select b (select (select b true) false))) 1.0 0.0)) (_ -zero 8 24) (fp.neg (_ -zero 8 24))))))
