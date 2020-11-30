; COMMAND-LINE: --nl-ext-purify
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)

(assert (and (not (<= skoX 0)) (and (not (<= (* (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX) (+ skoS3 skoSX)) 0)) (not (<= skoS3 0)))))


(check-sat)
(exit)
