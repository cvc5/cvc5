; COMMAND-LINE: --fmf-fun --no-check-models
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(define-fun BoolToString ((b Bool)) String (ite b "true" "false") )

(declare-datatypes () (
    (Color (red) (white) (blue))
) )

(define-fun ColorToString ((c Color)) String (ite (is-red c) "red" (ite (is-white c) "white" "blue")) )

(declare-datatypes () (
    (CP (cp (b Bool) (c Color)))
) )

(define-fun-rec CPToString ((cp CP)) String (str.++ "cp(" (BoolToString (b cp)) "," (ColorToString (c cp)) ")"))

(declare-fun CPFromString (String) CP)

(assert (forall ((cp1 CP)) (= cp1 (CPFromString (CPToString cp1)))))

(declare-fun cpx() CP)
(assert (= cpx (CPFromString "cp(true,white)")))

(check-sat)

