; REQUIRES: unrestricted-mode
; COMMAND-LINE: --rels-acyclic-hammer --rels-acyclic-unroll-max=4
;
; Regression test for --rels-acyclic-unroll-max: confirms a cap that is
; *sufficient* for the problem's actual cycle length does not interfere with
; ordinary solving. not_sc_mcm's cycle here needs exactly 4 elements, so
; doCycleInference's full-effort unrolling reaches that length entirely on
; its own before the cap (--rels-acyclic-unroll-max=4) would ever bind --
; checkAcyclicityLastCall's catch-up loop performs zero iterations. This does
; NOT exercise the catch-up mechanism itself (see the doc comment on
; TheorySetsRels::doCycleInference / checkAcyclicityLastCall): it guards
; against a different class of regression, e.g. an off-by-one in the
; >= vs > comparison used to decide whether the cap binds, which could cause
; a "big enough" cap to incorrectly restrict a problem it shouldn't affect at
; all. (tcgrounding-identity-sat.smt2 is the companion test exercising
; genuine catch-up with a cap strictly less than the required length --
; that needed a separate fix to TheorySetsRels::applyTCGroundingConflict
; first, see that file's own comment.)
(set-logic ALL)
(set-info :status sat)

(set-option :produce-models true)
; we need finite model finding to answer sat problems with universal
; quantified formulas
(set-option :finite-model-find true)
; we need sets extension to support set.universe operator
(set-option :sets-exp true)

(declare-sort Atom 0)
(declare-sort Thread 0)

(declare-fun iden () (Set (Tuple Atom Atom)))
(declare-fun univ () (Set (Tuple Atom)))
(declare-fun Address () (Set (Tuple Atom)))
(declare-fun Event () (Set (Tuple Atom)))
(declare-fun po () (Set (Tuple Atom Atom)))
(declare-fun address () (Set (Tuple Atom Atom)))
(declare-fun Read () (Set (Tuple Atom)))
(declare-fun Write () (Set (Tuple Atom)))
(declare-fun rf () (Set (Tuple Atom Atom)))
(declare-fun co () (Set (Tuple Atom Atom)))
(declare-fun fr () (Set (Tuple Atom Atom)))
(declare-fun Thread_set () (Set (Tuple Thread)))
(declare-fun thread (Atom) Thread)
(declare-fun rd_from_initial () (Set (Tuple Atom)))
(declare-fun addr_addr_set () (Set (Tuple Atom Atom)))

(define-fun irreflexive ((r (Set (Tuple Atom Atom)))) Bool
  (and
    (set.subset r (rel.product Event Event))
    (= (set.inter r iden) (as set.empty (Set (Tuple Atom Atom))))
  )
)

(define-fun transitive ((r (Set (Tuple Atom Atom)))) Bool
  (and
    (set.subset r (rel.product Event Event))
    (set.subset (rel.join r r) r)
  )
)

(define-fun total ((r (Set (Tuple Atom Atom))) (bag (Set (Tuple Atom)))) Bool
  (and
    (set.subset r (rel.product Event Event))
    (set.subset bag Event)
    (forall ((e1 Atom) (e2 Atom))
        (=> (and
                (not (= e1 e2))
                (set.member (tuple e1) bag)
                (set.member (tuple e2) bag))
            (set.member (tuple e1 e2) (set.union r (rel.transpose r)))
        )
    )
  )
)

(define-fun lone_set ((r (Set (Tuple Atom)))) Bool
  (or (set.is_singleton r) (= r (as set.empty (Set (Tuple Atom)))))
)

(define-fun not_sc_mcm () Bool
  (not (rel.acyclic (tuple rf po co fr)))
)

(assert (forall ((a Atom) (b Atom)) (and
  (=> (set.member (tuple a b) iden) (and (= a b) (set.member (tuple a) univ)))
  (=> (and (= a b) (set.member (tuple a) univ)) (set.member (tuple a b) iden))
  )))
(assert (forall ((a Atom)) (set.member (tuple a) univ)))
(assert (= (set.inter Event Address) (as set.empty (Set (Tuple Atom)))))
(assert (set.subset po (rel.product Event Event)))
(assert (forall ((e1 Atom) (e2 Atom) (e3 Atom))
  (=> (and (set.member (tuple e1 e2) po) (set.member (tuple e1 e3) po)) ; pre
      (= e2 e3) ; post
)))
(assert (set.subset address (rel.product Event Address)))
(assert (forall ((e1 Atom) (e2 Atom) (e3 Atom))
  (=> (and (set.member (tuple e1 e2) address) (set.member (tuple e1 e3) address)) ; pre
      (= e2 e3) ; post
)))
(assert (forall ((e1 Atom)) (=> (set.member (tuple e1) Event)
      (exists ((addr Atom)) (set.member (tuple e1 addr) address))))
)
(assert (= (set.inter Read Write) (as set.empty (Set (Tuple Atom)))))
(assert (= (set.union Read Write) Event))
(assert (set.subset rf (rel.product Write Read)))
(assert (set.subset co (rel.product Write Write)))

;; Same-thread events are po-ordered (one way or the other), or equal:
  ;;   thread(x) = thread(y)  =>  (x,y) in po+  \/  (y,x) in po+  \/  x = y
(assert (forall ((x Atom) (y Atom))
(=> (and (set.member (tuple x) Event) (set.member (tuple y) Event)
            (= (thread x) (thread y)))
    (or (set.member (tuple x y) (rel.tclosure po))
        (set.member (tuple y x) (rel.tclosure po))
        (= x y)))))

(assert (= (set.union Address Event) univ))
(assert (= rd_from_initial (set.minus Read (rel.join Write rf))))
(assert (forall ((e1 Atom) (e2 Atom))
  (=> (set.member (tuple e1 e2) addr_addr_set)
    (and (set.member (tuple e1) rd_from_initial) (set.member (tuple e2) Write))
  )))
(assert (forall ((e1 Atom) (e2 Atom))
  (=> (and (set.member (tuple e1) rd_from_initial) (set.member (tuple e2) Write))
    (set.member (tuple e1 e2) addr_addr_set)
  )))
(assert (= fr (set.union
  (rel.join (rel.transpose rf) co)
  addr_addr_set)))
(assert (set.subset fr (rel.product Read Write)))
(assert (forall ((e (Tuple Atom)) (r (Tuple Atom Atom)))
  (=> (set.member e Event)
      (lone_set (rel.join (set.singleton e) (rel.transpose po))))))
(assert (set.subset
  (set.union (set.union fr rf) co)  ; com
  (rel.join address (rel.transpose address))))
(assert (set.subset (rel.join rf (rel.transpose rf)) iden))
;; Vacuous (rf;rf = empty since rf subset Write x Read), but kept as a hint: it
;; registers (rel.tclosure rf) and equates rf+ with rf, so UnrollCycle-derived
;; memberships in rf+ are tied straight back to rf for the po+;rf template.
(assert (= rf (rel.tclosure rf)))
(assert (forall ((a (Tuple Atom)))
  (=> (set.member a Address)
      (total co (set.inter (rel.join (set.singleton a) (rel.transpose address)) Write)))))

;; Litmus test templates (same-address "po-loc" form, restored from the source):
(assert (rel.acyclic (tuple po)))
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  rf)))
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  co)))
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  fr)))

;; Single thread
(assert (forall ((e Atom)) (=> (set.member (tuple e) Event)
    (set.member (tuple (thread e)) Thread_set))))
(assert (set.is_singleton Thread_set))

;; Can we violate SC without the above litmus test templates:
(assert not_sc_mcm)

(check-sat)
