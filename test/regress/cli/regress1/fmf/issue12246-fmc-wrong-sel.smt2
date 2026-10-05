; REQUIRES: unrestricted-mode
; EXPECT: sat
; EXPECT: unsat
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :incremental true)
(set-option :fmf-fun true)
(declare-sort Ref 0)
(declare-const Ref.null Ref)
(declare-datatypes ((Snap 0)) (
  (
    (RefToSnap (SnapToRef Ref))
    (combine (first Snap) (second Snap))
  )
))
(declare-fun length%limited (Snap) Int)
(check-sat)
(define-funs-rec ((length%final ((s Snap)) Bool)) ((and
  (=
    (length%limited s)
    (+ 1 (ite (= (SnapToRef (first s)) Ref.null) 0 (length%limited (second s)))))
  (> (length%limited s) 0)
  (ite (= (SnapToRef (first s)) Ref.null) true (length%final (second s)))
)))
(declare-const t Snap)
(assert ((_ is combine) t))
(assert (length%final (first t)))
(assert (= (length%limited (first t)) 4))
(assert (not (= (SnapToRef (first (second (second (second (first t)))))) Ref.null)))
(check-sat)
