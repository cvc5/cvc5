(set-logic HO_ALL)
(set-option :tlimit 30000)
(set-option :produce-unsat-cores false)
(set-option :finite-model-find true)
(set-option :block-models literals)
(set-option :produce-models true)
(set-option :incremental true)
(set-option :sets-ext true)
(declare-sort Atom 0)
(declare-sort UInt 0)
(declare-fun intValue (UInt) Int)
(declare-fun atomNone () (Set (Tuple Atom)))
(declare-fun univAtom () (Set (Tuple Atom)))
(declare-fun idenAtom () (Set (Tuple Atom Atom)))
(declare-fun idenInt () (Set (Tuple UInt UInt)))
(declare-fun univInt () (Set (Tuple UInt)))
(declare-fun |this/Set | () (Set (Tuple Atom)))
(declare-fun |this/Element | () (Set (Tuple Atom)))
(declare-fun |integer/univInt | () (Set (Tuple UInt)))
(declare-fun |this/Set/elements | () (Set (Tuple Atom Atom)))

; Disjoint signatures
(assert 
 (= 
   (set.inter |this/Set | |this/Element |) atomNone))

; atomUniv is the union of top level signatures
(assert 
 (= 
   (set.union |this/Set | |this/Element |) univAtom))

; Top level signatures are disjoint
(assert 
 (= 
   (set.inter |this/Set | |this/Element |) atomNone))

; field (this/Set <: elements) multiplicity
(assert 
 (set.all 
 (lambda ((|this | (Tuple Atom)))
   (exists ((|_s_ | (Set (Tuple Atom)))) 
     (and 
          (and true 
            (set.subset |_s_ | |this/Element |)) 
          (and true true) 
          (= 
            (set.inter 
              (rel.product 
                (set.singleton |this |) univAtom) |this/Set/elements |) 
            (rel.product 
              (set.singleton |this |) |_s_ |)))))
  |this/Set |))

; field (this/Set <: elements) subset
(assert 
 (set.subset |this/Set/elements | 
   (rel.product |this/Set | |this/Element |)))

; SetGenerator
(assert 
 (and 
   (exists ((a.10 Atom)) 
     (let (
      (|s | 
       (tuple a.10))) 
       (and 
         (and true 
           (set.member |s | |this/Set |)) 
         (and true true) 
         (= 
           (rel.join
             (set.singleton |s |) |this/Set/elements |) 
           (as set.empty (Set (Tuple Atom))))))) 
   (set.all 
     (lambda 
       ((|s | (Tuple Atom))) 
       (set.all 
         (lambda 
           ((|e | (Tuple Atom)))
           (exists 
             ((a.13 Atom))
             (let ((|s' | (tuple a.13))) 
               (and 
                (set.member |s' | |this/Set |) 
                (= 
                  (rel.join (set.singleton |s' |) |this/Set/elements |)
                  (set.union 
                    (rel.join (set.singleton |s |) |this/Set/elements |) 
                    (set.singleton |e |)))))))
        |this/Element |))        
      |this/Set |)))

; Empty unary relation definition for Atom
(assert 
 (= atomNone 
   (as set.empty (Set (Tuple Atom)))))

; Universe definition for Atom
(assert 
 (= univAtom 
   (as set.universe (Set (Tuple Atom)))))

; Universe definition for UninterpretedInt
(assert 
 (= univInt 
   (as set.universe (Set (Tuple UInt)))))

; Identity relation definition
(assert 
 (set.all 
 (lambda ((t (Tuple Atom Atom))) (= ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
 idenAtom ))

; Identity relation definition
(assert 
 (set.all 
 (lambda ((t (Tuple UInt UInt))) (= ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
 idenInt ))

; intValue is injective
(assert 
 (forall ((x UInt)(y UInt)) 
   (=> 
     (not 
       (= x y)) 
     (not 
       (= (intValue x) (intValue y))))))

; integer/univInt = Int
(assert 
 (= |integer/univInt | univInt))

; (all x,y | x = y <=> x -> y in (integer/univInt <: idenInt))
(assert 
 (forall ((u.14 UInt)(u.15 UInt)) 
   (let (
    (|x | 
     (tuple u.14))
    (|y | 
     (tuple u.15))) 
     (=> 
       (and 
         (and 
           (and true 
             (set.member |x | |integer/univInt |)) 
           (set.member |y | |integer/univInt |)) 
         (and 
           (and true true) true)) 
       (= 
         (= 
           (set.singleton |x |) 
           (set.singleton |y |)) 
         (set.subset 
           (rel.product 
             (set.singleton |x |) 
             (set.singleton |y |)) idenInt))))))


; ! (all s0,s1 | (some s2 | s2 . (this/Set <: elements) = s0 . (this/Set <: elements) + s1 . (this/Set <: elements)))
(assert 
 (not 
   (set.all (lambda ((|s0 | (Tuple Atom)))   
         (set.all (lambda ((|s1 | (Tuple Atom)))
         (exists ((a.18 Atom)) 
           (let (
            (|s2 | 
             (tuple a.18))) 
             (and 
               (and true 
                 (set.member |s2 | |this/Set |)) 
               (and true true) 
               (= 
                 (rel.join
                   (set.singleton |s2 |) |this/Set/elements |) 
                 (set.union 
                   (rel.join
                     (set.singleton |s0 |) |this/Set/elements |) 
                   (rel.join
                     (set.singleton |s1 |) |this/Set/elements |))))))
         ) |this/Set |))
          |this/Set |)))


; Check Closed for 4 Element, 16 Set
(assert true)

(check-sat)


