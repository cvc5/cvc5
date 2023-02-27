(set-logic AUFBVFPDTNIRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

(declare-const bv (_ BitVec 32))
(assert (not (<= 0 (bv2nat bv))))

(check-sat)
