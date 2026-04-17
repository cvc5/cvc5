; EXPECT: sat
(set-logic AUFDTLIA)

(declare-datatypes ((Maybe 1))
  ((par (T) ((Nothing)
             (Just (value T))))))

(define-fun f ((optional (Maybe Int))) (Maybe Int)
  (match Nothing
    ((optional optional)
     ((Just value) (Just 1)))))

(declare-const c1 (Maybe Int))
(assert (= c1 (f (Just 1))))
(check-sat)
