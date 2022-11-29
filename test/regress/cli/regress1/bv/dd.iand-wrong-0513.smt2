; COMMAND-LINE: --solve-bv-as-int=iand --iand-mode=bitwise --nl-ext-tplanes
; EXPECT: sat
(set-logic ALL)
(declare-const a (_ BitVec 2))
(declare-const R (_ BitVec 2))
(declare-const t (_ BitVec 2))
(declare-const x Bool)
(assert 
(or 
(and (= (_ bv1 6) ((_ zero_extend 4) t)) (= ((_ zero_extend 4) a) (bvor ((_ zero_extend 4) t) ((_ zero_extend 4) R)))) 
x))
(assert 
(= (_ bv0 6) (bvand ((_ zero_extend 4) a) ((_ zero_extend 4) t)))
)
(check-sat)
