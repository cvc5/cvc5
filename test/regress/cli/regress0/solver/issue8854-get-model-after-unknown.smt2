; COMMAND-LINE: --rlimit-per=100
; SCRUBBER: sed 's/(define-fun .*)/define-fun/g'
; EXPECT: unknown
; EXPECT: (:reason-unknown resourceout)
; EXPECT: (
; EXPECT: define-fun
; EXPECT: define-fun
; EXPECT: define-fun
; EXPECT: )
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
(set-option :incremental true)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (<= 1 x))
(assert (<= 1 y))
(assert (<= 1 z))

(assert
  (not (not (= (+ (* (* x x) x) (* (* y y) y)) (* (* z z) z)))))

(assert
  (forall ((x1 Int) (y1 Int) (z1 Int))
    (=> (<= x1 y1) (=> (<= 0 z1) (<= (* x1 z1) (* y1 z1))))))

(check-sat)
(get-info :reason-unknown)
(get-model)
