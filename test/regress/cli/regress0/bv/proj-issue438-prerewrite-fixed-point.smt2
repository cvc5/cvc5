; Note: This benchmark triggers the same issue as
; proj-issue438-prerewrite-fixed-point-original.smt2, but for a different node
; kind.

(set-logic QF_BV)
(declare-const x (_ BitVec 3))
(define-fun z () (_ BitVec 3) (bvadd x x))
(define-fun s () (_ BitVec 3) (bvsub z z))
(assert (bvule (bvnand s s) s))
(set-info :status unsat)
(check-sat)
