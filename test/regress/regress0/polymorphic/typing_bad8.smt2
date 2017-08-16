; COMMAND-LINE: --quant-polymorphic
(set-logic UFLRA)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(declare-sort list 1)

(declare-fun nil (par (a) () (list a)))
(declare-fun cons (par (a) (a (list a)) (list a)))
(declare-fun length (par (a) ((list a)) Real))

(declare-sort I1 0)

(assert (= (length (as nil (list I1))) 0))

(assert (not (= (length nil) 0)))



(check-sat)
(exit)

; EXPECT: (error "Parse Error: typing_bad8.smt2:15.28: You should add an (as term ty) for specifying the return type.")
; EXIT: 1
