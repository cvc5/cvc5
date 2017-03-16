; COMMAND-LINE: --lang=smt2.6
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((IntList 0)) (
((empty) (insert ( head Int ) ( tail IntList ) ))
))

(declare-fun x () IntList)
(declare-fun y () IntList)
(declare-fun z () IntList)

(assert (distinct x y z))

(assert (not ((_ is insert) x)))
(assert (not ((_ is insert) y)))

(check-sat)
