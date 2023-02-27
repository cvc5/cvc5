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
(define-fun bound () Int (bv2nat ((_ int2bv 32) (^ 2 11))))

;assumptions
(assert (< (bv2nat x$) bound))
(assert (< (bv2nat y$) (^ 2 (+ 11 n$))))
(assert (< (bv2nat z$) (^ 2 16)))
(assert (< (bv2nat q$) bound))

;conclusion
(assert (not (< (div (+ (bv2nat x$) (bv2nat y$)) (^ 2 n$)) (^ 2 32))))
(check-sat)
