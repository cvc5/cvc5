; COMMAND-LINE: --solve-bv-as-int=iand
; EXPECT: unsat

(set-logic ALL)

(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(declare-const z (_ BitVec 16))

(assert
  (not
  (=>
    (bvule x y)
    (bvule (bvmul ((_ zero_extend 48) x) ((_ zero_extend 48) z)) (bvmul ((_ zero_extend 48) y) ((_ zero_extend 48) z))))))

(check-sat)
