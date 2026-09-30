; REQUIRES: unrestricted-mode
; Regression test for a soundness bug in the RELATION_ACYCLIC_DOWN rule
; (TheorySetsRels::applyAcyclicDownRule): the rule concluded a != b for the
; *representative* tuple (a,b) of a membership in TC(R), while its reason
; cited the membership of a syntactically different tuple (x,y) that was only
; equal to (a,b) in the current SAT context (e.g. after finite model finding
; merged atoms). Because inferences are context-independent lemmas, this
; produced lemmas such as ((w1,w2) in TC(po) /\ acyclic(po)) => false, which
; wrongly refuted the satisfiable execution
;   single thread  r -po-> w1 -po-> f -po-> w2,  co = {(w1,w2)},  rf = {(w2,r)}
; whose ghb = po-loc U rf U co U fr has the cycle r -> w1 -> w2 -> r while po
; itself is acyclic. Reduced (by delta debugging) from a memory-model litmus
; benchmark; the exact assertion set matters for the search path that
; triggered the bug. Expected: sat.
(set-info :status sat)
(set-logic ALL)
(set-option :produce-models true)
(set-option :finite-model-find true)
(set-option :sets-exp true)
(set-option :rels-exp true)
(declare-sort Atom 0)
(declare-sort Thread 0)
(declare-fun iden () (Set (Tuple Atom Atom)))
(declare-fun univ () (Set (Tuple Atom)))
(declare-fun Address () (Set (Tuple Atom)))
(declare-fun Event () (Set (Tuple Atom)))
(declare-fun MemEvent () (Set (Tuple Atom)))
(declare-fun Fence () (Set (Tuple Atom)))
(declare-fun Read () (Set (Tuple Atom)))
(declare-fun Write () (Set (Tuple Atom)))
(declare-fun po () (Set (Tuple Atom Atom)))
(declare-fun address () (Set (Tuple Atom Atom)))
(declare-fun rf () (Set (Tuple Atom Atom)))
(declare-fun co () (Set (Tuple Atom Atom)))
(declare-fun fr () (Set (Tuple Atom Atom)))
(declare-fun Thread_set () (Set (Tuple Thread)))
(declare-fun thread (Atom) Thread)
(declare-fun rd_from_initial () (Set (Tuple Atom)))
(declare-fun addr_addr_set () (Set (Tuple Atom Atom)))
(declare-fun loc () (Set (Tuple Atom Atom)))
(define-fun irreflexive ((r (Set (Tuple Atom Atom)))) Bool
  (and (set.subset r (rel.product Event Event))
       (= (set.inter r iden) (as set.empty (Set (Tuple Atom Atom))))))
(define-fun transitive ((r (Set (Tuple Atom Atom)))) Bool
  (and (set.subset r (rel.product Event Event))
       (set.subset (rel.join r r) r)))
(define-fun total ((r (Set (Tuple Atom Atom))) (bag (Set (Tuple Atom)))) Bool
  (and (set.subset r (rel.product MemEvent MemEvent))
       (set.subset bag MemEvent)
       (forall ((e1 Atom) (e2 Atom))
         (=> (and (not (= e1 e2))
                  (set.member (tuple e1) bag) (set.member (tuple e2) bag))
             (set.member (tuple e1 e2) (set.union r (rel.transpose r)))))
       (rel.acyclic (tuple r))))
(define-fun lone_set ((r (Set (Tuple Atom)))) Bool
  (or (set.is_singleton r) (= r (as set.empty (Set (Tuple Atom))))))
(assert (set.subset (set.union (set.union fr rf) co)
                    (rel.join address (rel.transpose address))))
(define-fun com () (Set (Tuple Atom Atom)) (set.union (set.union rf co) fr))
(define-fun po-loc () (Set (Tuple Atom Atom)) (set.inter po loc))
(define-fun ghb () (Set (Tuple Atom Atom)) (set.union po-loc com))
(define-fun mcm () Bool
  (and
    (rel.acyclic (tuple ghb))   
    (irreflexive com)   
  ))
(assert (rel.acyclic (tuple po)))
(declare-fun th0 () (Tuple Thread))
(assert (not mcm))
(declare-fun r () Atom)
(declare-fun w1 () Atom)
(declare-fun f () Atom)
(declare-fun w2 () Atom)
(declare-fun a () Atom)
(assert (= Fence (set.singleton (tuple f))))
(assert (= Read (set.singleton (tuple r))))
(assert (= Write (set.insert (tuple w1) (set.singleton (tuple w2)))))
(assert (= address (set.insert (tuple r a) (tuple w1 a) (set.singleton (tuple w2 a)))))
(assert (= po (set.insert (tuple r w1) (tuple w1 f) (set.singleton (tuple f w2)))))
(check-sat)
