; COMMAND-LINE: --fmf-fun
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-info :status sat)
(define-fun $$Bool.isTrue$$ ((b Bool)) Bool b)
(define-fun $$Bool.isFalse$$ ((b Bool)) Bool (not b))

(define-funs-rec
  (
    (f123454321$multipleArgsFunction((x$$645421 Bool) (y$$645422 Bool)) Bool)
    (f12345678$myConst() Int)
  )
  (
    (= x$$645421 y$$645422)
    3
  )
)

(declare-fun i1000$$1000() Bool)
(declare-fun i1001$$1001() Bool)
(declare-fun i1002$$1002() Int)
(assert (f123454321$multipleArgsFunction i1000$$1000 i1001$$1001))
(assert (= i1002$$1002 f12345678$myConst))
(check-sat)
