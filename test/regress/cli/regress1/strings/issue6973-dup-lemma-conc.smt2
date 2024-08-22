; COMMAND-LINE: --strings-exp
; COMMAND-LINE: --strings-exp --re-elim=agg
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun a () String)
(assert
 (str.in_re ""
  (re.++ (re.diff (re.comp re.all) (re.++ (str.to_re a) (re.comp re.all)))
   (str.to_re
    (ite
     (str.in_re ""
      (re.++ (str.to_re (ite (str.in_re "" (re.++ (str.to_re a) (re.comp re.all))) a ""))
       (re.inter (str.to_re a)
        (re.++ (str.to_re a)
         (re.comp (re.union (re.++ (str.to_re a) (re.comp re.all)) re.all))))))
     a "")))))
(check-sat)
