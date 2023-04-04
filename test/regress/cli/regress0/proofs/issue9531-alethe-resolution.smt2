; COMMAND-LINE: --dump-proofs --proof-format-mode=alethe --dag-thresh=0 --proof-granularity=theory-rewrite
; EXIT: 0
; SCRUBBER: grep -v -E '.*'
(set-logic QF_UF)
(declare-const x2 Bool)
(declare-const x Bool)
(declare-sort I 0)
(declare-fun u () I)
(declare-fun o (I I) I)
(declare-fun e () I)
(assert (or x x2))
(assert (or (= u (o u u)) (and (= u (o u u)) (or (not (= (o u (o u u)) (o (o (o e e) (o u (o u u))) (o e e)))) (= (o u (o u u)) (o (o e e) (o (o e e) (o u (o u u)))))))))
(assert (= (o e e) (o u u)))
(assert (or (= (o u (o u u)) (o (o e e) (o (o e e) (o u (o u u))))) (not (= (o u (o u u)) (o (o (o e e) (o u (o u u))) (o e e))))))
(assert (not (= (o u (o u u)) (o (o u u) (o (o e e) (o u (o u u)))))))
(check-sat)