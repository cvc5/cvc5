; COMMAND-LINE: --check-proofs --simplification=none --proof-annotate-theory-lemmas --dump-proofs --proof-format=none
; SCRUBBER: grep -o "ANNOTATE" | wc -l
; EXPECT: 3
; DISABLE-TESTER: lfsc
; DISABLE-TESTER: cpc
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const y (_ BitVec 2))
(declare-const x (_ BitVec 2))
(assert (not (not (and (= x #b01) (and (= y #b10) (= (bvadd x y) #b10))))))
(check-sat)
