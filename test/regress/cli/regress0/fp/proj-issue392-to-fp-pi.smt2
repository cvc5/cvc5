; REQUIRES: unrestricted-mode
; COMMAND-LINE: --produce-models -q
; EXPECT: sat
(set-logic ALL)
(set-option :fp-exp true)
(declare-const _x3 Real)
(assert (let ((_let0 ((_ to_fp 5 11) roundNearestTiesToEven real.pi)))(not (and (is_int _x3) (fp.eq _let0 _let0)))))
(check-sat)
