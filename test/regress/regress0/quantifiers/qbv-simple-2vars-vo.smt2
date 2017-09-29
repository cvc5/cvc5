; COMMAND-LINE: --cbqi-bv
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))

(assert (not (= a #x00000000)))

; this is sensitive to variable ordering (try changing x and y)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) (or 
(not (= (bvmul x y) #x0000000A))
(not (= (bvadd y a) #x00000010))
)))

(check-sat)
