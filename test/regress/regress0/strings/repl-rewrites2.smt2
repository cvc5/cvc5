; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(assert (or
(not (= (str.replace "" "" "c") ""))
(not (= (str.replace (str.++ "abc" y) "b" x) (str.++ "a" x "c" y)))
(not (= (str.replace "" "abc" "de") ""))
(not (= (str.replace "ab" "ab" "de") "de"))
(not (= (str.replace "ab" "" "de") "ab"))
))
(check-sat)
