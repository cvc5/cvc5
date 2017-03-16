; COMMAND-LINE: --lang=smt2.6
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ( ( Tree 0) ( TreeList 0) ) (
 ( ( node ( value Int ) ( children TreeList) ))
( ( empty ) ( insert ( head Tree) ( tail TreeList)) )
))


(declare-fun t () TreeList)
(assert (<= 100 (match t ((empty (- 1)) ((insert x1 x2) (value x1))))))

(check-sat)
