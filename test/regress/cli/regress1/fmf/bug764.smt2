; COMMAND-LINE: --fmf-fun
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(set-info :status sat)

(define-fun BoolToString ((b Bool)) String (ite b "true" "false") )

(declare-datatypes ((Color 0)) (
    ((red) (white) (blue))
))

(define-fun ColorToString ((c Color)) String (ite ((_ is red) c) "red" (ite ((_ is white) c) "white" "blue")) )

(declare-datatypes ((CP 0)) (
    ((cp (b Bool) (c Color)))
))

(define-fun-rec CPToString ((cp CP)) String (str.++ "cp(" (BoolToString (b cp)) "," (ColorToString (c cp)) ")"))

(declare-fun CPFromString (String) CP)

(assert (forall ((cp1 CP)) (= cp1 (CPFromString (CPToString cp1)))))

(declare-fun cpx () CP)
(assert (= cpx (CPFromString "cp(true,white)")))

(check-sat)
