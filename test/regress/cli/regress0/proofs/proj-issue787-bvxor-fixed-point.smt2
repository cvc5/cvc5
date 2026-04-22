; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(declare-fun x () (_ BitVec 4))
(assert (not (=
  (bvand #b1011
         (bvand x
                (bvor (bvxor (bvxor x (bvnot x) x (_ bv1 4) x)
                             (bvnot x)
                             x
                             x
                             x)
                      x
                      x
                      (bvand (bvadd #x2 x x) x))
                      x
                      x)
                #b1110)
         (bvand #b1010 x))))
(check-sat)
