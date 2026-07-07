; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic QF_BVLIA)
(set-info :status unsat)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(declare-const d (_ BitVec 32))
(declare-const e (_ BitVec 32))

(assert (or (= a b) (= a c) (= a d) (= a e)))

(assert (not (= (ubv_to_int a) (ubv_to_int b))))
(assert (not (= (ubv_to_int a) (ubv_to_int c))))
(assert (not (= (ubv_to_int a) (ubv_to_int d))))
(assert (not (= (ubv_to_int a) (ubv_to_int e))))

(check-sat)
