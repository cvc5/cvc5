; COMMAND-LINE: -q
; EXPECT: sat
(set-logic QF_ADTNIA)
(set-info :status sat)
(declare-sort u 0)
(declare-sort u1 0)
(declare-datatypes ((d 3)) ((par (p _p p5) ((c (s u1)) (_c (_s p) (e p) (se u))))))
(declare-const x u)
(declare-const _x (d Int Int Int))
(declare-const x4 (d u1 Int u))
(declare-const x6 (d u Int u1))
(assert (and (> (_s ((_ update se) _x x)) 0) (match ((_ update s) x6 (s x4)) (((_c _x64 _x65 _x66) (> (_s ((_ update se) _x x)) 0)) (_x67 true)))))
(check-sat)
