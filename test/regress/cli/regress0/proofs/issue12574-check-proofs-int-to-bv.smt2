; EXPECT: unsat
(set-logic UFBVSLIA)
(declare-fun s (String String Int) String)
(declare-const e String)
(assert (= 1
  (ite (str.in_re (s (str.from_int 0) (str.from_int 0) 0) re.allchar)
       0
       (ubv_to_int ((_ int_to_bv 1) 1)))))
(assert (forall ((b String))
  (= (= 1
        (+ 0
           (ubv_to_int
             (bvand ((_ int_to_bv 2) 1)
                    ((_ int_to_bv 2)
                     (str.indexof
                       (ite (str.in_re e re.allchar) e (str.from_int 0))
                       "."
                       0))))))
     (= 1 (str.len b)))))
(assert (= e ""))
(check-sat)
