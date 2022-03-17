; COMMAND-LINE: --incremental --fmf-fun
; DISABLE-TESTER: model
(set-logic UFDTLIA)
(set-option :produce-models true)
(declare-datatypes ((List 0)) (((Nil) (Cons (Cons$head Int) (Cons$tail List)))))
(define-fun-rec all-z ((x List)) Bool (=> ((_ is Cons) x) (and (= 0 (Cons$head x)) (all-z (Cons$tail x)))))
(define-fun-rec len ((x List)) Int (ite ((_ is Nil) x) 0 (+ 1 (len (Cons$tail x)))))
(declare-fun root() List)
; EXPECT: sat
(assert (and (all-z root) (<= 1 (len root))))
(check-sat)
; EXPECT: sat
(assert (= root (Cons 0 Nil)))
(check-sat)

