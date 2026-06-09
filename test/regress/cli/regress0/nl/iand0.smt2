; DISABLE-TESTER: dump
; EXPECT:
; SCRUBBER: grep -v "iand.must.be"
; REQUIRES: no-competition
; EXIT: 1
(set-logic QF_ANIA)
(declare-const x Bool)
(declare-const x2 Bool)
(declare-fun x_ () Int)
(declare-fun _5 () (Array Int Int))
(declare-fun _6 () (Array Int Int))
(declare-fun _7 () (Array Int Int))
(declare-fun _73 () (Array Int Int))
(declare-fun _76 () Int)
(assert (or x2 x))
(assert (= 0 (select _6 ((_ iand 0) 1 x_))))
(assert (or (= _73 _6) (and x2 (= _73 (store _6 _76 1))) (= _7 (store _5 0 0))))
(assert (or x (and (= _6 _5) (= _76 (select _7 0)))))
(assert (or x (= _73 (store _5 0 0))))
(check-sat)
