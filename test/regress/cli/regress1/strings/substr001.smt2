; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(set-info :status sat)

(declare-fun x () String)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun i4 () Int)

(assert (and (>= i1 0) (>= i2 0) (< (+ i1 i2) (str.len x))))
(assert (and (>= i3 0) (>= i4 0) (< (+ i3 i4) (str.len x))))
(assert (= "efg" (str.substr x i1 i2) ) )
(assert (= "bef" (str.substr x i3 i4) ) )
(assert (> (str.len x) 5))

(check-sat)
