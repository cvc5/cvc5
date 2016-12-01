; COMMAND-LINE: --incremental --fmf-fun-rlv --no-check-models
(set-logic ALL_SUPPORTED)

(declare-datatypes () (
    (Color (red) (white) (blue))
) )

(define-fun ColorToString ((c Color)) String (ite (is-red c) "red" (ite (is-white c) "white" "blue")) )
(declare-fun ColorFromString (String) Color)
(assert (forall ((c Color)) (= c (ColorFromString (ColorToString c)))))

(declare-datatypes () (
    (CP (cp (c1 Color) (c2 Color)))
) )

(define-fun-rec CPToString ((cp CP)) String (str.++ "cp(" (ColorToString (c1 cp)) "," (ColorToString (c2 cp)) ")"))
(declare-fun CPFromString (String) CP)
(assert (forall ((cp1 CP)) (= cp1 (CPFromString (CPToString cp1)))))

(declare-fun cpx() CP)
(assert (= cpx (CPFromString "cp(white,red)")))

; EXPECT: sat
(check-sat)

(declare-fun cpy() CP)
(assert (= cpy (CPFromString "cp(red,blue)")))

; EXPECT: sat
(check-sat)
