; COMMAND-LINE: --lang=smt2.6
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ( ( Tree 1) ( TreeList 1) ) (
(par ( X ) ( ( node ( value X ) ( children ( TreeList X )) )))
(par ( Y ) ( ( empty ) ( insert ( head ( Tree Y )) ( tail ( TreeList Y ))) ))
))


(declare-fun x () (Tree Int))
(declare-fun y () (Tree Int))
(declare-fun z () (Tree Int))


(assert (distinct x y z))
(assert (= (value x) 5))
(assert ((_ is insert) (children y)))
(assert (= (value (head (children y))) 7))

(declare-sort U 0)
(declare-fun a () (Tree U))
(declare-fun b () (Tree U))
(declare-fun c () (Tree U))

(assert (distinct a b c))

(assert ((_ is insert) (children a)))


(declare-fun d () (Tree (Tree Int)))
(declare-fun e () (Tree (Tree Int)))
(declare-fun f () (Tree (Tree Int)))

(assert (distinct d e f))

(check-sat)
