; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; EXPECT: (error "Parse Error:
; EXIT: 1
(set-logic AUFDTLIA)

(declare-datatypes ((Maybe 1))
  ((par (T) ((Nothing)
             (Just (value T))))))

(define-fun f ((optional (Maybe Int))) (Maybe Int)
  (match optional
    ((Nothing Nothing)
     ((Just value) (Just value)))))

(declare-const c1 (Maybe Int))
(assert (= c1 (f (Just 1))))
;(assert (= c1 Nothing))

(check-sat)
