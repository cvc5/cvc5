; REQUIRES: cocoa
; EXPECT: sat
(set-logic QF_FF)
(set-option :incremental true)

(define-sort F () (_ FiniteField 7))
(declare-fun a () F)
(declare-fun c () F)
(declare-fun pre () Bool)
(declare-fun suf () Bool)

; pre : c == a + 1
(assert (= pre (= c (ff.add a (as ff1 F))))) 

; suf : -a == -c + 1
(assert (= suf (= (ff.mul (as ff6 F) a) (ff.add (ff.mul (as ff6 F) c) (as ff1 F)))))

(assert (and pre suf))

(check-sat)
