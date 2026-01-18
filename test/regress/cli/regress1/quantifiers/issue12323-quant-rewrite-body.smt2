; EXPECT: unsat
(set-logic ALL)

(declare-fun get_sep_count (String String) Int)

(define-fun get_suffix_after_sep ((input_str String) (sep String) (flag Int)) String
  (let ((sep_idx (str.indexof input_str sep 0)))
    (ite (< flag 0)
         (str.++ "NO_SEP_" input_str)
         (let ((start_pos (+ sep_idx (str.len sep))))
           (str.substr input_str start_pos (- (str.len input_str) start_pos))))))

(define-fun get_suffix ((input_str String) (sep String) (flag Int)) String
  (let ((suffix (get_suffix_after_sep input_str sep flag)))
    (ite (str.contains suffix sep)
         (str.substr input_str 0 1)
         suffix)))

(declare-const target_str String)
(assert (= target_str ""))

(assert 
  (not 
    (exists ((index Int))
       (or 
         (< index (get_sep_count "" "|"))
         (and 
           (= (get_suffix_after_sep target_str "|" index) "") 
           (= (get_suffix target_str "|" index) "")
         )
       )
    )
  )
)

(check-sat)
