; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; ERROR-SCRUBBER: sed -e 's/.*//g'
; EXPECT: (error "Parse Error:
; EXIT: 1

(declare-datatypes ((Maybe 1))
  ((par (T) ((Nothing)
             (Just (value T))))))

(define-fun f ((optional (Maybe Int))) (Maybe Int)
  (match Nothing
    ((optional optional)
     ((Just value) (Just 1)))))

(assert (= c1 (f (Just 1))))
(check-sat)
