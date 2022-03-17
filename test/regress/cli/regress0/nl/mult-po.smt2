; COMMAND-LINE: --nl-ext=full
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)

(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)

(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))

(assert (and (> a b) (> b c) (> c d)))

(assert (< (* a d) (* b c)))

(check-sat)
