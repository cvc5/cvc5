; REQUIRES: cocoa
; REQUIRES: poly
; COMMAND-LINE: --nl-cov-lift=lazard
; EXPECT: sat
(set-logic QF_NRA)
(declare-const d Real)
(declare-const a Real)
(declare-const m Real)
(declare-const l Real)
(declare-const t Real)
(declare-const x Real)
(declare-const y Real)
(declare-const v Real)
(assert (and
    (< m 0)
    (< d 0)
    (> y 0)
    (> t 0)
    (= 0 (+ m x (* l v)))
    (= 0 (+ x a (* a y)))
    (= 0 (+ t (* d d) (* t t) (* a a y) (- (* d l v y y))))
))
(check-sat)
