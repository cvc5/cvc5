; COMMAND-LINE: --solve-bv-as-int=sum --nl-ext-tplanes 
; EXPECT: unsat
; causes exception with large exponents on some builds
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(declare-fun x$ () (_ BitVec 32))
(declare-fun y$ () (_ BitVec 32))
(declare-fun z$ () (_ BitVec 32))
(declare-fun q$ () (_ BitVec 32))
(declare-fun n$ () Int)
(assert (>= n$ 0))
(define-fun bound () Int (ubv_to_int ((_ int_to_bv 32) (int.pow2 11))))

;assumptions
(assert (< (ubv_to_int x$) bound))
(assert (< (ubv_to_int y$) (int.pow2 (+ 11 n$))))
(assert (< (ubv_to_int z$) (int.pow2 16)))
(assert (< (ubv_to_int q$) bound))

;conclusion
(assert (not (< (div (+ (ubv_to_int x$) (ubv_to_int y$)) (int.pow2 n$)) (int.pow2 32))))
(check-sat)
