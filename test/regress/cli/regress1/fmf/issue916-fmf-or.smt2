; COMMAND-LINE: --fmf-fun
; EXPECT: sat
; DISABLE-TESTER: model

(set-logic UFDTLIA)
(set-info :smt-lib-version 2.6)

(define-funs-rec
  (
    (validIdValue ((x Int)(v Int)) Bool)
  )
  (
    (or 
        (and (= x 0) (< (- 10) v 10) )
        (and (= x 1) (<= (- 100) v (- 10)) )
        (and (= x 2) (<= 10 v 100) )
        (and (= x 3) (< (- 1000) v (- 100)) )
        (and (= x 4) (< 100 v 1000) )
        (and (= x 5) (<= (- 1000) v) )
        (and (= x 6) (<= v 1000) )
            (validIdValue (- x 7) v)
    )
  )
)

(declare-datatypes ((List 1)) ((par (T)((Nil) (Cstr (head T) (tail (List T)))))))
(declare-datatypes ((Pair 2)) ((par (T S)((Pair (first T) (second S))))))

(define-funs-rec
  (
    (validList ((l (List (Pair Int Int)))) Bool)
  )
  (
    (ite (= l (as Nil (List (Pair Int Int))) )
        true
        (let ((hd (head l))) (and (>= (first hd) 0) 
                                  (validIdValue (first hd) (second hd)) 
                                  (validList (tail l))
                              )
        )
    )
  )
)


(declare-const myList (List (Pair Int Int)))
(assert (distinct myList (as Nil (List (Pair Int Int)))))
(assert (validList myList))
(check-sat)
