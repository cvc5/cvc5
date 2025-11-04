; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((__ 0)) (((v))))
(declare-datatypes ((c 0)) (((c (u __)))))
(declare-fun d () c)
(declare-fun d2 () c)
(check-sat-assuming ((not (= d d2))))
