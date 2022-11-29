; COMMAND-LINE: --learned-rewrite
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof

;
;!(a,b,c).( 0<=b & 1<=c & 0<=a & 1<=c
;               =>
;               (a+(b mod c)) mod c = (a+b) mod c)
;
(set-logic QF_NIA)
(set-option :print-success false)

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

(assert (<= 0 a))
(assert (<= 1 c))
(assert (<= 0 b))

(assert (! (not (= (mod (+ a (mod b c)) c) (mod (+ a b) c))) :named goal))
(check-sat)
(exit)
