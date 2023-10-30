; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic QF_UFLIA)
(set-option :produce-abducts true)
(set-option :sygus-core-connective false)
(declare-sort A 0)
(declare-datatype List (par (E)
  ((nil)
   (cons (hd E) (tl (List E))))))
(declare-fun a () A) ;a
(declare-fun app ((List A) (List A)) (List A)) ;++
(declare-fun y () (List A)) ;y
(declare-fun x () (List A)) ;x
(get-abduct X (not (= (as nil (List A)) (app x y))))
