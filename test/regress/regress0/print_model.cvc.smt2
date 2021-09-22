; COMMAND-LINE: --produce-models
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun s1 () Int 2)
; EXPECT: (define-fun s2 () Int 1)
; EXPECT: )
(set-logic ALL)
(set-option :incremental true)
(set-option :produce-models true)
(declare-fun s1 () Int)
(declare-fun s2 () Int)
(assert (= s1 2))
(push 1)

(assert (and (> s2 0) (< s2 s1)))

(check-sat)
(get-model)

(pop 1)
