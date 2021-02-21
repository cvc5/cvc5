; COMMAND-LINE: --strings-exp
; EXPECT: sat
; EXPECT: (((seq.nth y 7) 404))
; EXPECT: (((str.from_code x) "?"))
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () (Seq Int))

(assert (< (seq.len y) 5))

(assert (= x 63))

(assert (= (seq.nth y 7) 404))

(check-sat)

(get-value ((seq.nth y 7)))
(get-value ((str.from_code x)))
