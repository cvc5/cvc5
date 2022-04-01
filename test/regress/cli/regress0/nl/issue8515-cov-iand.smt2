; REQUIRES: poly
; SCRUBBER: grep -o "Term of kind iand is not compatible"
; EXPECT: Term of kind iand is not compatible
; EXIT: 1
(set-logic ALL)
(set-option :nl-cov true)
(set-option :check-models true)
(declare-fun v () Int)
(declare-fun a () Int)
(declare-fun va () Int)
(assert (and (= 1 (div 0 va)) (> 0 ((_ iand 1) v a))))
(check-sat)
