(set-option :check-models true)
(declare-const x (_ FiniteField 13))
(check-sat)
(get-value ((ff.add (ff.mul x x) (ff.mul (ff.mul #f93m13 (ff.neg #f93m13)) (ff.add #f93m13 (ff.mul x x) (ff.mul #f93m13 (ff.neg #f93m13)))) (ff.mul (ff.mul #f93m13 (ff.neg #f93m13)) (ff.add #f93m13 (ff.mul x x) (ff.mul #f93m13 (ff.neg #f93m13)))) (ff.mul (ff.mul #f93m13 (ff.neg #f93m13)) (ff.add #f93m13 (ff.mul x x) (ff.mul #f93m13 (ff.neg #f93m13)))))))

