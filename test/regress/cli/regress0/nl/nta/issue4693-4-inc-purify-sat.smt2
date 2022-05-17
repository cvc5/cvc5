; COMMAND-LINE: -i --no-debug-check-models
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-const v0 Bool)
(declare-const v7 Bool)
(declare-const v12 Bool)
(declare-const r11 Real)
(declare-const bv_17-0 (_ BitVec 17))
(declare-const r14 Real)
(assert (xor (>= 98766.0 (cos r11) r14) v12 (= #x1e #x1e #x1e) v0 (= (concat (bvxor (_ bv860 10) (_ bv860 10) (_ bv860 10)) bv_17-0) (concat (bvxor (_ bv860 10) (_ bv860 10) (_ bv860 10)) bv_17-0) (concat (bvxor (_ bv860 10) (_ bv860 10) (_ bv860 10)) bv_17-0)) v7))
(push 1)
(check-sat)
(pop 1)
(check-sat)
