; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic ALL)
(declare-fun s$ () (_ BitVec 32))
(declare-fun x$ () (_ BitVec 32))
(declare-fun i$ () (_ BitVec 32))
(define-fun bound () Int (ubv_to_int ((_ int_to_bv 32) 2048)))
(define-fun bseg ((x (_ BitVec 32)) (s (_ BitVec 32))) Bool (and (< (ubv_to_int x) bound) (<= (+ (ubv_to_int x) (ubv_to_int s)) bound)))

;assumptions
(assert (bseg x$ s$))
(assert (<= (ubv_to_int i$) (ubv_to_int s$)))

;conclusion
(assert (not (= (ubv_to_int (bvadd x$ i$)) (+ (ubv_to_int x$) (ubv_to_int i$)))))
(check-sat)
