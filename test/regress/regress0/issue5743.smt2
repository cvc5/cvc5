; COMMAND-LINE: --check-models -q
(set-logic QF_AUFBV)
(set-info :status sat)
(declare-fun bv_22-0 () (_ BitVec 1))
(declare-fun arr-8324605531633220487_-1461211092162269148-0 () (Array (_ BitVec 1) Bool))
(assert (select arr-8324605531633220487_-1461211092162269148-0 (bvlshr bv_22-0 bv_22-0)))
(check-sat)
