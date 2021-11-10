; EXPECT: sat
(set-logic QF_ALL)
(set-info :status sat)

; Observed behavior
;
; Benchmark taking too long. Lemmas being generated indefinitely with
; skolems due to the "two sets not being equal" axiom.
;
; What was the bug?
;
;

(define-sort Elt () Int)
(define-sort mySet () (Set Elt))

(declare-fun f (Int) mySet)
(declare-fun x () Int)
(declare-fun y () Int)

(declare-fun S () mySet)
(declare-fun T () mySet)

(assert (= (f x) 
           (set.union S T)))

(assert (= (f x) 
           (set.union T (f y))))

(assert (not (= (f y) 
                (set.union T (f y)))))

(check-sat)
