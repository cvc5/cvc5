; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun x () (Pair Int Real) ((as mkPair (Pair Int Real)) 2 (/ 3 2)))
; EXPECT: )

(set-logic ALL)
(set-option :produce-models true)
(set-info :status sat)
(declare-datatypes ( (Pair 2) ) (
(par ( X Y ) ( (mkPair (first X) (second Y))))
))


(declare-fun x () (Pair Int Real))

(assert (= x (mkPair 2 1.5)))

(check-sat)
(get-model)
