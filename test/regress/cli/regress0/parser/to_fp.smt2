; COMMAND-LINE: --strict-parsing
; EXPECT: sat
(set-logic QF_FP)
(declare-fun |c::main::main::3::div@1!0&0#1| () (_ FloatingPoint 8 24))
(assert (not (fp.eq ((_ to_fp 11 53)
                     roundNearestTiesToEven
                     |c::main::main::3::div@1!0&0#1|)
              (fp #b0 #b00000000000 #x0000000000000))))
(check-sat)
