; COMMAND-LINE: --seq-array=lazy
(set-logic QF_SLIA)
(declare-fun s () (Seq Int))
(declare-fun j () Int)
(assert (and 
  (= (seq.unit 0) (str.update s 0 (seq.unit 0)))
  (distinct
    (seq.nth s j)
    (seq.nth (seq.unit (seq.nth s 0)) j))))
(set-info :status unsat)
(check-sat)
