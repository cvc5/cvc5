; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the fresh elements the star needs cannot be read back into a bag.map or
; bag.filter term, see BagSolver::collectLiastarModelValues, so the model is
; marked unsound and the answer is unknown, although the problem is sat
; COMMAND-LINE: --bags-to-liastar
; EXPECT: unknown
(set-logic HO_ALL)
(set-info :status sat)
(set-option :fmf-bound true)
; A bags version of a query over an event trace, where the sum over the
; deduplicated aggregation rows is compared against the sum over the events
; themselves. The two disagree as soon as two matching events carry the same
; amount, e.g. for two transfers of 50 against a threshold of 100, where the
; deduplicated sum is 50 and the per event sum is 100.
;
; Two things are needed to solve it, and neither is enough on its own. First,
; the aggregation rows are a composition of operators rather than the two
; containments of the original query, one universal and one universal over an
; existential: those reduce to a bag.filter whose predicate captures the outer
; bound variable, so every candidate row adds another filter term over the
; event trace, and no configuration answers that form. Second, the translation
; to liastar, which turns the cardinality of the bag.setof term into
; arithmetic over the cardinality of its argument. The same composition of
; operators written with sets is not answered by the sets solver, which cannot
; even derive that a set.map does not grow a set.

; ---- event-trace relations ----
(declare-fun R_Alert () (Bag (Tuple Int Int Int)))
(declare-fun R_Transfer () (Bag (Tuple Int Int Int Int)))
; ---- decision request ----
(declare-const q (Tuple Int Int Int))

; the matching window of a transfer against the request q
(define-fun P ((e0 (Tuple Int Int Int Int))) Bool
  (and (or (< ((_ tuple.select 2) e0) ((_ tuple.select 1) q))
           (and (= ((_ tuple.select 2) e0) ((_ tuple.select 1) q))
                (<= ((_ tuple.select 3) e0) ((_ tuple.select 2) q))))
       (<= (- ((_ tuple.select 1) q) 3600) ((_ tuple.select 2) e0))
       (= ((_ tuple.select 0) e0) ((_ tuple.select 0) q))))
; the aggregated column of a transfer
(define-fun amount ((e0 (Tuple Int Int Int Int))) (Tuple Int)
  (tuple ((_ tuple.select 1) e0)))

(assert (bag.all (lambda ((t (Tuple Int Int Int)))
  (and (>= ((_ tuple.select 1) t) 0) (>= ((_ tuple.select 2) t) 0))) R_Alert))
(assert (bag.member q R_Alert))
(assert (bag.all (lambda ((t (Tuple Int Int Int Int)))
  (and (>= ((_ tuple.select 2) t) 0) (>= ((_ tuple.select 3) t) 0))) R_Transfer))
(assert (>= ((_ tuple.select 1) q) 0))
(assert (>= ((_ tuple.select 2) q) 0))

; the deduplicated sum and the per event sum disagree on the threshold. The
; aggregation rows are the setof of the amounts of the matching transfers.
(assert (not (=
  (>= (bag.fold (lambda ((r (Tuple Int)) (a Int)) (+ a ((_ tuple.select 0) r))) 0
        (bag.setof (bag.map amount (bag.filter P R_Transfer)))) 100)
  (>= (bag.fold (lambda ((fe (Tuple Int Int Int Int)) (a Int)) (+ a ((_ tuple.select 1) fe))) 0
        (bag.filter P R_Transfer)) 100))))
(check-sat)
