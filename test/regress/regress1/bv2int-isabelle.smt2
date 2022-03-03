; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic ALL)
(declare-fun s$ () (_ BitVec 32))
(declare-fun x$ () (_ BitVec 32))
(declare-fun i$ () (_ BitVec 32))
(define-fun bound () Int (bv2nat ((_ int2bv 32) 2048)))
(define-fun bseg ((x (_ BitVec 32)) (s (_ BitVec 32))) Bool (and (< (bv2nat x) bound) (<= (+ (bv2nat x) (bv2nat s)) bound)))

;assumptions
(assert (bseg x$ s$))
(assert (<= (bv2nat i$) (bv2nat s$)))

;conclusion
(assert (not (= (bv2nat (bvadd x$ i$)) (+ (bv2nat x$) (bv2nat i$)))))
(check-sat)
