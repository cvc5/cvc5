(set-logic ALL)
(set-info :status unsat)
(set-option :cegqi-all false)
(set-option :produce-unsat-cores true)
(set-option :block-models literals)
(set-option :finite-model-find true)
(set-option :produce-models true)
(set-option :tlimit-per 30000)
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
(declare-fun |this/Time | () (Set (Tuple UInt)))
(declare-fun |this/BankAccount | () (Set (Tuple Atom)))
(declare-fun |integer/univInt | () (Set (Tuple UInt)))
(declare-fun a.1 () Atom)
(declare-fun |this/BankAccount/deposit | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/withdrawal | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/balance | () (Set (Tuple Atom UInt UInt)))
(declare-fun u.9_0 () UInt)
(declare-fun u.11_1 () UInt)
(define-fun |this/init | ((|t | (Tuple UInt))) Bool

 (and
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/deposit |; (this/BankAccount <: deposit)
        )
       (singleton |t |))
     (singleton
       (mkTuple u.9_0)))
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
        )
       (singleton |t |))
     (singleton
       (mkTuple u.9_0)))
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/balance |; (this/BankAccount <: balance)
        )
       (singleton |t |))
     (singleton
       (mkTuple u.9_0)))))
(define-fun |this/depositValue | ((|t | (Tuple UInt))) (Tuple UInt)

 (choose
   (join
     (join |this/BankAccount |; this/BankAccount
       |this/BankAccount/deposit |; (this/BankAccount <: deposit)
      )
     (singleton |t |))))
(define-fun |this/withdrawalValue | ((|t | (Tuple UInt))) (Tuple UInt)

 (choose
   (join
     (join |this/BankAccount |; this/BankAccount
       |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
      )
     (singleton |t |))))
(define-fun |this/balanceValue | ((|t | (Tuple UInt))) (Tuple UInt)

 (choose
   (join
     (join |this/BankAccount |; this/BankAccount
       |this/BankAccount/balance |; (this/BankAccount <: balance)
      )
     (singleton |t |))))
(define-fun |this/deposit | ((|t | (Tuple UInt))(|t' | (Tuple UInt))(|amount | (Tuple UInt))) Bool

 (and
   (> (intValue ((_ tupSel 0) |amount |)) (intValue u.9_0))
   (= (|this/depositValue | |t' |) |amount |)
   (= (|this/withdrawalValue | |t' |)
     (mkTuple u.9_0))
   (exists ((z UInt))
     (and
       (=
         (+ (intValue ((_ tupSel 0) (|this/balanceValue | |t |))) (intValue ((_ tupSel 0) |amount |))) (intValue z; integer/plus[this/balanceValue[t], amount]
        ))
       (= (|this/balanceValue | |t' |)
         (mkTuple z; integer/plus[this/balanceValue[t], amount]
          ))))))
(define-fun |this/withdraw | ((|t | (Tuple UInt))(|t' | (Tuple UInt))(|amount | (Tuple UInt))) Bool

 (and
   (> (intValue ((_ tupSel 0) |amount |)) (intValue u.9_0))
   (>= (intValue ((_ tupSel 0) (|this/balanceValue | |t |))) (intValue ((_ tupSel 0) |amount |)))
   (= (|this/depositValue | |t' |)
     (mkTuple u.9_0))
   (= (|this/withdrawalValue | |t' |) |amount |)
   (exists ((z UInt))
     (and
       (=
         (- (intValue ((_ tupSel 0) (|this/balanceValue | |t |))) (intValue ((_ tupSel 0) |amount |))) (intValue z; integer/minus[this/balanceValue[t], amount]
        ))
       (= (|this/balanceValue | |t' |)
         (mkTuple z; integer/minus[this/balanceValue[t], amount]
          ))))))
(define-fun |this/someTransaction | ((|t | (Tuple UInt))(|t' | (Tuple UInt))) Bool

 (exists ((u.37 UInt))
   (let (
    (|amount |
     (mkTuple u.37)))
     (and
       (member |amount | univInt; Int
        )
       (= (|this/deposit | |t | |t' | |amount |)
         (not (|this/withdraw | |t | |t' | |amount |)))))))
(define-fun |this/system | () Bool

 (and (|this/init |
   (mkTuple u.9_0))
   (forall ((u.38 UInt))
     (let (
      (|t' |
       (mkTuple u.38)))
       (=>
         (member |t' | |this/Time |; this/Time
          )
         (=>
           (not
             (= |t' |
               (mkTuple u.9_0)))
           (exists ((z UInt))
             (and
               (=
                 (- (intValue u.38) (intValue u.11_1)) (intValue z; integer/minus[t', Int[1]]
                ))
               (let (
                (|t | z; integer/minus[t', Int[1]]
                )) (|this/someTransaction |
                 (mkTuple |t |; t
                  ) |t' |))))))))))
(define-fun |this/nonNegative | ((|t | (Set (Tuple UInt)))) Bool

 (and
   (>= (intValue ((_ tupSel 0) (|this/depositValue |
     (choose |t |; t
      )))) (intValue u.9_0))
   (>= (intValue ((_ tupSel 0) (|this/withdrawalValue |
     (choose |t |; t
      )))) (intValue u.9_0))
   (>= (intValue ((_ tupSel 0) (|this/balanceValue |
     (choose |t |; t
      )))) (intValue u.9_0))))

; one this/BankAccount
(assert (!
 (= |this/BankAccount |; this/BankAccount

   (singleton
     (mkTuple a.1)))
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":9,"y1":4,"x2":51,"y2":10,"symbolIndex":22}|))

; atomUniv is the union of top level signatures
(assert (!
 (= |this/BankAccount |; this/BankAccount
   univAtom)
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":9,"y1":4,"x2":51,"y2":10,"symbolIndex":23}|))

; field (this/BankAccount <: deposit) multiplicity
(assert (!
 (forall ((x Atom))
   (=>
     (member
       (mkTuple x) |this/BankAccount |; this/BankAccount
      )
     (forall ((y UInt))
       (=>
         (member
           (mkTuple y) |this/Time |; this/Time
          )
         (exists ((z UInt))
           (and
             (member
               (mkTuple z) univInt; Int
              )
             (member
               (mkTuple x z y) |this/BankAccount/deposit |; (this/BankAccount <: deposit)
              )
             (forall ((w UInt))
               (=>
                 (not
                   (= w z))
                 (not
                   (member
                     (mkTuple x w y) |this/BankAccount/deposit |; (this/BankAccount <: deposit)
                    ))))))))))
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":5,"y1":6,"x2":28,"y2":6,"symbolIndex":24}|))

; field (this/BankAccount <: deposit) subset
(assert (!
 (subset |this/BankAccount/deposit |; (this/BankAccount <: deposit)

   (product |this/BankAccount |; this/BankAccount

     (product univInt; Int
       |this/Time |; this/Time
      )))
 :named |{"filename":"","x1":1,"y1":1,"x2":1,"y2":1,"symbolIndex":25}|))

; field (this/BankAccount <: withdrawal) multiplicity
(assert (!
 (forall ((x Atom))
   (=>
     (member
       (mkTuple x) |this/BankAccount |; this/BankAccount
      )
     (forall ((y UInt))
       (=>
         (member
           (mkTuple y) |this/Time |; this/Time
          )
         (exists ((z UInt))
           (and
             (member
               (mkTuple z) univInt; Int
              )
             (member
               (mkTuple x z y) |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
              )
             (forall ((w UInt))
               (=>
                 (not
                   (= w z))
                 (not
                   (member
                     (mkTuple x w y) |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
                    ))))))))))
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":5,"y1":7,"x2":30,"y2":7,"symbolIndex":26}|))

; field (this/BankAccount <: withdrawal) subset
(assert (!
 (subset |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)

   (product |this/BankAccount |; this/BankAccount

     (product univInt; Int
       |this/Time |; this/Time
      )))
 :named |{"filename":"","x1":1,"y1":1,"x2":1,"y2":1,"symbolIndex":27}|))

; field (this/BankAccount <: balance) multiplicity
(assert (!
 (forall ((x Atom))
   (=>
     (member
       (mkTuple x) |this/BankAccount |; this/BankAccount
      )
     (forall ((y UInt))
       (=>
         (member
           (mkTuple y) |this/Time |; this/Time
          )
         (exists ((z UInt))
           (and
             (member
               (mkTuple z) univInt; Int
              )
             (member
               (mkTuple x z y) |this/BankAccount/balance |; (this/BankAccount <: balance)
              )
             (forall ((w UInt))
               (=>
                 (not
                   (= w z))
                 (not
                   (member
                     (mkTuple x w y) |this/BankAccount/balance |; (this/BankAccount <: balance)
                    ))))))))))
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":5,"y1":8,"x2":27,"y2":8,"symbolIndex":28}|))

; field (this/BankAccount <: balance) subset
(assert (!
 (subset |this/BankAccount/balance |; (this/BankAccount <: balance)

   (product |this/BankAccount |; this/BankAccount

     (product univInt; Int
       |this/Time |; this/Time
      )))
 :named |{"filename":"","x1":1,"y1":1,"x2":1,"y2":1,"symbolIndex":29}|))

; Signature fact 'AND[some this/BankAccount . (this/BankAccount <: deposit), some this/BankAccount . (this/BankAccount <: withdrawal), some this/BankAccount . (this/BankAccount <: balance)]' for sig this/BankAccount
(assert (!
 (forall ((|this | Atom))
   (=>
     (member
       (mkTuple |this |) |this/BankAccount |; this/BankAccount
      )
     (and
       (not
         (=
           (join |this/BankAccount |; this/BankAccount
             |this/BankAccount/deposit |; (this/BankAccount <: deposit)
            )
           (as emptyset (Set (Tuple UInt UInt)))))
       (not
         (=
           (join |this/BankAccount |; this/BankAccount
             |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
            )
           (as emptyset (Set (Tuple UInt UInt)))))
       (not
         (=
           (join |this/BankAccount |; this/BankAccount
             |this/BankAccount/balance |; (this/BankAccount <: balance)
            )
           (as emptyset (Set (Tuple UInt UInt))))))))
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":1,"y1":10,"x2":51,"y2":10,"symbolIndex":30}|))

; constant integer
(assert
 (= (intValue u.9_0) 0))

; nonNegative
(assert (!
 (forall ((u.51 UInt))
   (let (
    (|t |
     (mkTuple u.51)))
     (=>
       (member |t | |this/Time |; this/Time
        )
       (>= (intValue u.51) (intValue u.9_0)))))
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":1,"y1":2,"x2":39,"y2":2,"symbolIndex":31}|))

; constant integer
(assert
 (= (intValue u.11_1) 1))

; noGaps
(assert (!
 (forall ((u.52 UInt))
   (let (
    (|t |
     (mkTuple u.52)))
     (=>
       (member |t | |this/Time |; this/Time
        )
       (exists ((z UInt))
         (and
           (=
             (- (intValue u.52) (intValue u.11_1)) (intValue z; integer/minus[t, Int[1]]
            ))
           (=>
             (not
               (= |t |
                 (mkTuple u.9_0)))
             (member
               (mkTuple z; integer/minus[t, Int[1]]
                ) |this/Time |; this/Time
              )))))))
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":1,"y1":3,"x2":62,"y2":3,"symbolIndex":32}|))

; fact$3
(assert (! |this/system |
 :named |{"filename":"/home/mudathir/Desktop/org.alloytools.alloy/SMT-Extension/test/course/bank_account.als","x1":1,"y1":61,"x2":13,"y2":61,"symbolIndex":33}|))

; universe
(assert (!
 (= |integer/univInt |; integer/univInt
   univInt; Int
  )
 :named |{"filename":"/$alloy4$/models/util/integer.als","x1":1,"y1":117,"x2":30,"y2":117,"symbolIndex":34}|))

; identity
(assert (!
 (forall ((u.53 UInt)(u.54 UInt))
   (let (
    (|y |
     (mkTuple u.54))
    (|x |
     (mkTuple u.53)))
     (=>
       (and
         (member |x | |integer/univInt |; integer/univInt
          )
         (member |y | |integer/univInt |; integer/univInt
          ))
       (=
         (= |x | |y |)
         (subset
           (product
             (singleton |x |)
             (singleton |y |)) idenInt; (integer/univInt <: idenInt)
          )))))
 :named |{"filename":"/$alloy4$/models/util/integer.als","x1":1,"y1":118,"x2":63,"y2":118,"symbolIndex":35}|))

; Empty unary relation definition for Atom
(assert
 (= atomNone
   (as emptyset (Set (Tuple Atom)))))

; Universe definition for Atom
(assert
 (= univAtom
   (as univset (Set (Tuple Atom)))))

; Universe definition for UninterpretedInt
(assert
 (= univInt; Int

   (as univset (Set (Tuple UInt)))))

; Identity relation definition for idenAtom
(assert
 (forall ((a.1 Atom)(a.2 Atom))
   (=
     (member
       (mkTuple a.1 a.2) idenAtom)
     (= a.1 a.2))))

; Identity relation definition for idenInt
(assert
 (forall ((u.3 UInt)(u.4 UInt))
   (=
     (member
       (mkTuple u.3 u.4) idenInt; (integer/univInt <: idenInt)
      )
     (= u.3 u.4))))

; intValue is injective
(assert
 (forall ((x UInt)(y UInt))
   (=>
     (not
       (= x y))
     (not
       (= (intValue x) (intValue y))))))

; ! (all t',a | t' != 0 => (let t= integer/minus[t', Int[1]] | this/withdraw[t, t', a] => int[this/balanceValue[t']] < int[this/balanceValue[t]]))
(assert
 (not
   (forall ((u.55 UInt)(u.56 UInt))
     (let (
      (|t' |
       (mkTuple u.55))
      (|a |
       (mkTuple u.56)))
       (=>
         (and
           (member |t' | |this/Time |; this/Time
            )
           (member |a | |integer/univInt |; integer/univInt
            ))
         (=>
           (not
             (= |t' |
               (mkTuple u.9_0)))
           (exists ((z UInt))
             (and
               (=
                 (- (intValue u.55) (intValue u.11_1)) (intValue z; integer/minus[t', Int[1]]
                ))
               (let (
                (|t | z; integer/minus[t', Int[1]]
                ))
                 (=> (|this/withdraw |
                   (mkTuple |t |; t
                    ) |t' | |a |)
                   (< (intValue ((_ tupSel 0) (|this/balanceValue | |t' |))) (intValue ((_ tupSel 0) (|this/balanceValue |
                     (mkTuple |t |; t
                      )))))))))))))))

(check-sat)
