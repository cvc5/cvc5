(set-logic HO_ALL)

(set-info :status sat)

(define-fun truthRelation () (Relation String String String)
  (set.union
   (set.singleton (tuple "A" "X" "0"))
   (set.singleton (tuple "A" "X" "1"))
   (set.singleton (tuple "A" "Y" "0"))
   (set.singleton (tuple "A" "Y" "1"))
   (set.singleton (tuple "B" "X" "0"))
   (set.singleton (tuple "B" "X" "1"))
   (set.singleton (tuple "B" "Y" "0"))
   (set.singleton (tuple "B" "Y" "1"))))

; parition by first column
(assert
 (= ((_ rel.group 0) truthRelation)
    (set.union
     (set.singleton
      (set.union (set.singleton (tuple "A" "X" "0"))
                 (set.singleton (tuple "A" "X" "1"))
                 (set.singleton (tuple "A" "Y" "0"))
                 (set.singleton (tuple "A" "Y" "1"))))
     (set.singleton
      (set.union (set.singleton (tuple "B" "X" "0"))
                 (set.singleton (tuple "B" "X" "1"))
                 (set.singleton (tuple "B" "Y" "0"))
                 (set.singleton (tuple "B" "Y" "1")))))))

; parition by second column
(assert
 (= ((_ rel.group 1) truthRelation)
    (set.union
     (set.singleton
      (set.union (set.singleton (tuple "A" "X" "0"))
                 (set.singleton (tuple "A" "X" "1"))
                 (set.singleton (tuple "B" "X" "0"))
                 (set.singleton (tuple "B" "X" "1"))))
     (set.singleton
      (set.union (set.singleton (tuple "A" "Y" "0"))
                 (set.singleton (tuple "A" "Y" "1"))
                 (set.singleton (tuple "B" "Y" "0"))
                 (set.singleton (tuple "B" "Y" "1")))))))

; parition by third column
(assert
 (= ((_ rel.group 2) truthRelation)
    (set.union
     (set.singleton
      (set.union (set.singleton (tuple "A" "X" "0"))
                 (set.singleton (tuple "A" "Y" "0"))
                 (set.singleton (tuple "B" "X" "0"))
                 (set.singleton (tuple "B" "Y" "0"))))
     (set.singleton
      (set.union (set.singleton (tuple "A" "X" "1"))
                 (set.singleton (tuple "A" "Y" "1"))
                 (set.singleton (tuple "B" "X" "1"))
                 (set.singleton (tuple "B" "Y" "1")))))))

; parition by first,second columns
(assert
 (= ((_ rel.group 0 1) truthRelation)
    (set.union
     (set.singleton
      (set.union (set.singleton (tuple "A" "X" "0"))
                 (set.singleton (tuple "A" "X" "1"))))
     (set.singleton
      (set.union (set.singleton (tuple "A" "Y" "0"))
                 (set.singleton (tuple "A" "Y" "1"))))
     (set.singleton
      (set.union (set.singleton (tuple "B" "X" "0"))
                 (set.singleton (tuple "B" "X" "1"))))
     (set.singleton
      (set.union (set.singleton (tuple "B" "Y" "0"))
                 (set.singleton (tuple "B" "Y" "1")))))))

; parition by no column
(assert
 (= (rel.group truthRelation)
    (set.singleton
     (set.union
      (set.singleton (tuple "A" "X" "0"))
      (set.singleton (tuple "A" "X" "1"))
      (set.singleton (tuple "A" "Y" "0"))
      (set.singleton (tuple "A" "Y" "1"))
      (set.singleton (tuple "B" "X" "0"))
      (set.singleton (tuple "B" "X" "1"))
      (set.singleton (tuple "B" "Y" "0"))
      (set.singleton (tuple "B" "Y" "1"))))))

; parition by all columns
(assert
 (= ((_ rel.group 0 1 2) truthRelation)
    (set.union
     (set.singleton (set.singleton (tuple "A" "X" "0")))
     (set.singleton (set.singleton (tuple "A" "X" "1")))
     (set.singleton (set.singleton (tuple "A" "Y" "0")))
     (set.singleton (set.singleton (tuple "A" "Y" "1")))
     (set.singleton (set.singleton (tuple "B" "X" "0")))
     (set.singleton (set.singleton (tuple "B" "X" "1")))
     (set.singleton (set.singleton (tuple "B" "Y" "0")))
     (set.singleton (set.singleton (tuple "B" "Y" "1"))))))

; group of set.empty
(assert
 (= ((_ rel.group 0) (as set.empty (Relation String String String)))
    (set.singleton (as set.empty (Relation String String String)))))

(check-sat)
