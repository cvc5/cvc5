; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=1
; EXPECT: (error "Error in option parsing: --solve-bv-as-int=bitwise does not support quantifiers")
; EXIT: 1
(set-logic BV)
(declare-const x (_ BitVec 8))
(assert (forall ((y (_ BitVec 8)))
               (distinct #b00000000
                         (bvand x y))))
(check-sat)
