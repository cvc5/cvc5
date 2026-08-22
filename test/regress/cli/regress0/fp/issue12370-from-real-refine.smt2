; COMMAND-LINE:
; COMMAND-LINE: --check-unsat-cores
; EXPECT: sat
(set-logic ALL)
(declare-fun s (Real) Real)
(declare-fun h () Real)
(assert (and (> (+ h (to_real (ubv_to_int #x4330000000000000))) 0.0) (< (+ h (to_real (ubv_to_int #x4330000000000000))) 1.0)))
(assert (= 0.0 (+ (s 0.0) (ite (fp.isNormal ((_ to_fp 8 24) RNE h)) 1.0 (abs 0.0)))))
(check-sat)
