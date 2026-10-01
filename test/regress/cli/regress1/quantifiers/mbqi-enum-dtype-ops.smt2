; COMMAND-LINE: --mbqi --mbqi-enum
; EXPECT: unsat
(set-logic ALL)

(declare-datatypes ((struct.0 0))
  (((mk-struct.0 (struct.0.coeffs (Array (_ BitVec 64) (_ BitVec 16)))))))
(declare-datatypes ((struct.2 0))
  (((mk-struct.2 (struct.2.vec (Array (_ BitVec 64) struct.0))))))

(declare-fun arr () (Array (_ BitVec 64) struct.0))
(declare-fun s2 () struct.2)

(assert
  (forall ((j (_ BitVec 32)))
    (and
      (= (select arr ((_ zero_extend 32) j))
         (mk-struct.0 (struct.0.coeffs (select arr ((_ zero_extend 32) j)))))
      (= (select (struct.2.vec s2) (_ bv0 64))
         (select arr ((_ zero_extend 32) j)))
      (bvsge
        ((_ sign_extend 16)
          (select (struct.0.coeffs (select arr ((_ zero_extend 32) j)))
                  (_ bv0 64)))
        (_ bv0 32)))))

(assert
  (not (bvsge ((_ sign_extend 16)
                (select (struct.0.coeffs (select arr (_ bv0 64))) (_ bv0 64)))
              (_ bv0 32))))

(check-sat)
