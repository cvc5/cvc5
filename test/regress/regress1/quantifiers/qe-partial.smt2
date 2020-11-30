; SCRUBBER: sed -e 's/(not (>= (+ .* (\* (- 1) .*)) 1))$/(not (>= (+ TERMA (\* (- 1) TERMB)) 1))/'
; EXPECT: (not (>= (+ TERMA (* (- 1) TERMB)) 1))
(set-logic LIA)
(set-info :status unsat)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(get-qe-disjunct (exists ((x Int)) (and (<= a x) (or (<= x b) (<= x c)))))
