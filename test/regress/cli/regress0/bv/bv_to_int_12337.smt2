; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: 
; SCRUBBER: grep -v "uninterpreted"
; EXIT: 1
(set-logic ALL)
(declare-const __ (_ BitVec 5))
(declare-const o (_ BitVec 3))
(declare-const m (_ BitVec 1))
(declare-const s (_ BitVec 1))
(declare-const b (_ BitVec 1))
(declare-fun f ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun a ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun r ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (or (= (_ bv0 8) (a (_ bv0 8) ((_ zero_extend 7) s) ((_ zero_extend 7) m))) (= (_ bv0 8) (r x ((_ zero_extend 7) b) ((_ zero_extend 3) __)))))
(assert (or (forall ((VAR2 (_ BitVec 8))) (exists ((VAR3 (_ BitVec 8))) (exists ((VAR4 (_ BitVec 8))) (forall ((VAR0 (_ BitVec 8))) (= (_ bv1 8) (r (a (f VAR0 VAR2 (_ bv3 8)) (bvadd VAR3 ((_ zero_extend 5) o)) VAR4) ((_ zero_extend 3) __) x))))))))
(assert (= (_ bv16 8) ((_ zero_extend 3) __)))
(assert (= x (_ bv224 8)))
(assert (= (_ bv5 8) ((_ zero_extend 5) o)))
(check-sat)
