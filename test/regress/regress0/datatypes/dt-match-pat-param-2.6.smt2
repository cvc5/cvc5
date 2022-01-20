; COMMAND-LINE: --lang=smt2.6
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ( ( Tree 0) ( TreeList 0) ) (
 ( ( node ( value Int ) ( children TreeList) ))
( ( empty ) ( set.insert ( head Tree) ( tail TreeList)) )
))


(declare-fun t () TreeList)
(assert (<= 100 (match t ((empty (- 1)) ((set.insert x1 x2) (value x1))))))


(declare-datatypes ( ( PTree 1) ( PTreeList 1) ) (
(par ( X ) ( ( pnode ( pvalue X ) ( pchildren ( PTreeList X )) )))
(par ( Y ) ( ( pempty ) ( pinsert ( phead ( PTree Y )) ( ptail ( PTreeList Y ))) ))
))

(declare-fun pt () (PTreeList Int))
(assert (<= 200 (match pt ((pempty (- 1)) ((pinsert x1 x2) (pvalue x1))))))


(check-sat)
