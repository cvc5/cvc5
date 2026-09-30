; REQUIRES: unrestricted-mode
; COMMAND-LINE: --rels-acyclic-hammer --rels-acyclic-unroll-max=3
;
; Regression test for a soundness bug in TheorySetsRels::applyTCGroundingConflict
; (used by checkTransitiveClosureLastCall under --rels-acyclic-hammer): its
; antecedent fixed tc_rel[0]'s value (rel = union of known members), which
; correctly guards against rel's own membership changing later, but did not
; account for mem_rep's *element identities* changing. If mem_rep's first
; component (e.g. a fresh cycle-witness skolem introduced by
; applyInstCycleRule/applyUnrollCycle) is merely a *different representative*
; from rel's known sources -- not *provably disequal* from them -- the
; learned clause is not actually a valid tautology: there exists a model
; where that skolem is later (soundly) identified with one of those sources,
; making the membership genuinely justified without rel's value ever
; changing, while the permanently-learned clause still incorrectly forces
; `false` in that branch. This file has a genuine satisfying model requiring
; not_sc_mcm's cycle-witness elements to be identified with concrete graph
; nodes; under the old buggy implementation this could resolve to an
; unconfirmed "unsat" instead of "sat" (with --rels-acyclic-unroll-max=3
; specifically) or simply time out (with any cap, or none at all -- this
; bug's spurious permanently-learned conflicts made the search substantially
; harder even when they didn't cause an outright wrong answer). Fixed by
; adding mem_rep[0]'s disequality from every known source of tc_rel[0] as an
; explicit antecedent conjunct, unconditionally -- regardless of whether that
; disequality is currently provable. This keeps the clause a tautology in
; all cases: if the disequality later turns out false (the skolem gets
; identified with a source), that antecedent conjunct is false and the
; clause is simply inactive rather than unsound.
; This also serves as the "genuine catch-up" companion to
; unroll-max-sufficient-cap-sat.smt2: the cap here (3) is strictly less than
; not_sc_mcm's required cycle length (4).
(set-logic ALL)
(set-info :status sat)

(set-option :produce-models true)
; we need finite model finding to answer sat problems with universal
; quantified formulas
(set-option :finite-model-find true)
; we need sets extension to support set.universe operator
(set-option :sets-exp true)

;; (set-option :produce-unsat-cores true)
;; (set-option :produce-proofs true)



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
;; === ADDED FOR FULL: modification order (mo / coherence "co") and from-read (fr) ===
(declare-fun co () (Set (Tuple Atom Atom)))
(declare-fun fr () (Set (Tuple Atom Atom)))
;; === END ADDED ===
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

;; === ADDED FOR FULL: helpers needed to constrain co (transitive + per-address total) ===
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
    ;; (rel.acyclic (tuple r))
  )
)
;; === END ADDED ===

(define-fun lone_set ((r (Set (Tuple Atom)))) Bool
  (or (set.is_singleton r) (= r (as set.empty (Set (Tuple Atom)))))
)

(define-fun not_sc_mcm () Bool
  ;; === CHANGED FOR FULL: SC = acyclic(rf U po U co U fr)  (was rf U po) ===
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
;; === ADDED FOR FULL: co relates writes to writes ===
(assert (set.subset co (rel.product Write Write)))
;; === END ADDED ===

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
  ; This may be a bug -- do we need to say that e1 and e2 are to the same address?
(assert (forall ((e1 Atom) (e2 Atom))
  (=> (and (set.member (tuple e1) rd_from_initial) (set.member (tuple e2) Write))
    (set.member (tuple e1 e2) addr_addr_set)
  )))
;; === ADDED FOR FULL: fr = (rf^-1 ; co) U addr_addr_set ; fr relates reads to writes ===
(assert (= fr (set.union
  (rel.join (rel.transpose rf) co)
  addr_addr_set)))
(assert (set.subset fr (rel.product Read Write)))
;; === END ADDED ===
(assert (forall ((e (Tuple Atom)) (r (Tuple Atom Atom)))
  (=> (set.member e Event)
      (lone_set (rel.join (set.singleton e) (rel.transpose po))))))
;; === CHANGED FOR FULL: com = fr U rf U co must stay within same-address (was just rf) ===
(assert (set.subset
  (set.union (set.union fr rf) co)  ; com
  (rel.join address (rel.transpose address))))
;; === END CHANGED ===
(assert (set.subset (rel.join rf (rel.transpose rf)) iden))
;; Vacuous (rf;rf = empty since rf subset Write x Read), but kept as a hint: it
;; registers (rel.tclosure rf) and equates rf+ with rf, so UnrollCycle-derived
;; memberships in rf+ are tied straight back to rf for the po+;rf template.
(assert (= rf (rel.tclosure rf)))
;; (assert (= fr (rel.tclosure fr)))
;; === ADDED FOR FULL: co is transitive and a total order on each address's writes ===
(assert (transitive co))
(assert (forall ((a (Tuple Atom)))
  (=> (set.member a Address)
      (total co (set.inter (rel.join (set.singleton a) (rel.transpose address)) Write)))))
;; === END ADDED ===

;; Litmus test templates (same-address "po-loc" form, restored from the source):
(assert (rel.acyclic (tuple po)))
;; === CHANGED FOR FULL: each template is  irreflexive( (po+ ∩ same-address) ; X )
;;     for X in {rf, co, fr}.  (acyclic9 used the simpler  irreflexive(po+ ; rf).) ===
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  rf)))
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  co)))
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  fr)))
;; === END CHANGED ===

;; Single thread
;; thread_range = { thread(e) | e in Event }
(assert (forall ((e Atom)) (=> (set.member (tuple e) Event)
    (set.member (tuple (thread e)) Thread_set))))
(assert (set.is_singleton Thread_set))

;; Can we violate SC without the above litmus test templates:
(assert not_sc_mcm)

(check-sat)
