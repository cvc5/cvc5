(set-logic HO_ALL)

(set-info :status sat)

(define-fun truthTable () (Table String String String)
  (bag.union_disjoint
   (bag (tuple "A" "X" "0") 2)
   (bag (tuple "A" "X" "1") 2)
   (bag (tuple "A" "Y" "0") 2)
   (bag (tuple "A" "Y" "1") 2)
   (bag (tuple "B" "X" "0") 2)
   (bag (tuple "B" "X" "1") 2)
   (bag (tuple "B" "Y" "0") 2)
   (bag (tuple "B" "Y" "1") 2)))

; parition by first column
(assert
 (= ((_ table.group 0) truthTable)
    (bag.union_disjoint
     (bag
      (bag.union_disjoint (bag (tuple "A" "X" "0") 2)
                          (bag (tuple "A" "X" "1") 2)
                          (bag (tuple "A" "Y" "0") 2)
                          (bag (tuple "A" "Y" "1") 2))
      1)
     (bag
      (bag.union_disjoint (bag (tuple "B" "X" "0") 2)
                          (bag (tuple "B" "X" "1") 2)
                          (bag (tuple "B" "Y" "0") 2)
                          (bag (tuple "B" "Y" "1") 2))
      1))))

; parition by second column
(assert
 (= ((_ table.group 1) truthTable)
    (bag.union_disjoint
     (bag
      (bag.union_disjoint (bag (tuple "A" "X" "0") 2)
                          (bag (tuple "A" "X" "1") 2)
                          (bag (tuple "B" "X" "0") 2)
                          (bag (tuple "B" "X" "1") 2))
      1)
     (bag
      (bag.union_disjoint (bag (tuple "A" "Y" "0") 2)
                          (bag (tuple "A" "Y" "1") 2)
                          (bag (tuple "B" "Y" "0") 2)
                          (bag (tuple "B" "Y" "1") 2))
      1))))

; parition by third column
(assert
 (= ((_ table.group 2) truthTable)
    (bag.union_disjoint
     (bag
      (bag.union_disjoint (bag (tuple "A" "X" "0") 2)
                          (bag (tuple "A" "Y" "0") 2)
                          (bag (tuple "B" "X" "0") 2)
                          (bag (tuple "B" "Y" "0") 2))
      1)
     (bag
      (bag.union_disjoint (bag (tuple "A" "X" "1") 2)
                          (bag (tuple "A" "Y" "1") 2)
                          (bag (tuple "B" "X" "1") 2)
                          (bag (tuple "B" "Y" "1") 2))
      1))))

; parition by first,second columns
(assert
 (= ((_ table.group 0 1) truthTable)
    (bag.union_disjoint
     (bag
      (bag.union_disjoint (bag (tuple "A" "X" "0") 2)
                          (bag (tuple "A" "X" "1") 2))
      1)
     (bag
      (bag.union_disjoint (bag (tuple "A" "Y" "0") 2)
                          (bag (tuple "A" "Y" "1") 2))
      1)
     (bag
      (bag.union_disjoint (bag (tuple "B" "X" "0") 2)
                          (bag (tuple "B" "X" "1") 2))
      1)
     (bag
      (bag.union_disjoint (bag (tuple "B" "Y" "0") 2)
                          (bag (tuple "B" "Y" "1") 2))
      1))))

; parition by no column
(assert
 (= (table.group truthTable)
    (bag
     (bag.union_disjoint
      (bag (tuple "A" "X" "0") 2)
      (bag (tuple "A" "X" "1") 2)
      (bag (tuple "A" "Y" "0") 2)
      (bag (tuple "A" "Y" "1") 2)
      (bag (tuple "B" "X" "0") 2)
      (bag (tuple "B" "X" "1") 2)
      (bag (tuple "B" "Y" "0") 2)
      (bag (tuple "B" "Y" "1") 2))
     1)))

; parition by all columns
(assert
 (= ((_ table.group 0 1 2) truthTable)
    (bag.union_disjoint
     (bag (bag (tuple "A" "X" "0") 2) 1)
     (bag (bag (tuple "A" "X" "1") 2) 1)
     (bag (bag (tuple "A" "Y" "0") 2) 1)
     (bag (bag (tuple "A" "Y" "1") 2) 1)
     (bag (bag (tuple "B" "X" "0") 2) 1)
     (bag (bag (tuple "B" "X" "1") 2) 1)
     (bag (bag (tuple "B" "Y" "0") 2) 1)
     (bag (bag (tuple "B" "Y" "1") 2) 1))))

(check-sat)
