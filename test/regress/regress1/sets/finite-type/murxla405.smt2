(set-logic ALL)
(set-info :status sat)
(set-option :global-declarations true)
(set-option :sets-ext true)

(check-sat-assuming
 (((_ divisible 1341480107) (set.card (as set.universe (Set (_ BitVec 117)))))
   ((_ divisible 1341480107) (set.card (as set.universe (Set (_ BitVec 117)))))
   ((_ divisible 1341480107) (set.card (as set.universe (Set (_ BitVec 117)))))
   ((_ divisible 1341480107) (set.card (as set.universe (Set (_ BitVec 117)))))
   ((_ divisible 1341480107) (set.card (as set.universe (Set (_ BitVec 117)))))))
