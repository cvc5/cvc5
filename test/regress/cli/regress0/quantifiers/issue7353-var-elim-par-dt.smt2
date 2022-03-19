(set-logic ALL)
(set-info :status sat)
(declare-datatype Option (par (T) ((none) (some (extractSome T)))))
(assert
 (forall ((x (Option Int)))
         (=> (and ((_ is some) x)
                  (= (extractSome x) 0))
             (= x (some 0)))))
(check-sat)
