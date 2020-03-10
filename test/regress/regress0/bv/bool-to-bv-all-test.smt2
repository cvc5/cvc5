; COMMAND-LINE: --bool-to-bv=all
; EXPECT: sat
; checks for a bug that can occur when forcing booleans to
;  bit-vectors when other sorts are present
(set-logic QF_ABV)

(declare-const A (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const B (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const sel Bool)
(declare-const idx (_ BitVec 32))
(declare-const val (_ BitVec 32))

(assert (=> sel (bvult idx (_ bv15 32))))
(assert (=> (= A (store B idx val)) sel))
(assert (=> (= A (store B idx val)) (not (= idx val))))
(assert (not (= A B)))
(assert (=> (not (= A (store B idx val))) (not sel)))
(assert (=> (not (= A (store B idx val))) (bvugt idx val)))

(check-sat)
