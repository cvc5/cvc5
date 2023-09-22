; COMMAND-LINE: --produce-difficulty
; SCRUBBER: sed 's/).*/)/g'
; EXPECT: sat
; EXPECT: (
; EXPECT: ((distinct a b c)
; EXPECT: ((=> (R a)
; EXPECT: )

; EXIT: 0

(set-logic ALL)
(set-option :finite-model-find true)
(set-option :fmf-mbqi none)
(set-option :produce-difficulty true)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (distinct a b c))
(declare-fun P (U U) Bool)
(declare-fun R (U) Bool)
(declare-fun S (U) Bool)

(define-fun Q () Bool (forall ((x U) (y U)) (P x y)))

(assert (or (not Q) (S a)))
(assert (R a))
(assert (=> (R a) Q))

; This example will instantiate the quantified formula 9 times, hence the
; explanation for why it is relevant will be incremented by 9.
; The explanation for why Q is relevant should be (=> (R b) Q) and 
; not (or (not Q) (S a)), since the former is the reason it is asserted true.

(check-sat)
(get-difficulty)
