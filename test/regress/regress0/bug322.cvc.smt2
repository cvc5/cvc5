; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((UNIT 0)) (((Unit))))
(declare-datatypes ((BOOL 0)) (((Truth) (Falsity))))
(declare-sort node$type 0)
(declare-sort value$type 0)

(declare-sort Nodes$t$type 0)


(define-fun is_faulty ((p node$type) (deliver (Array node$type (Array node$type BOOL)))) BOOL (ite (exists ((q node$type)) (not (= (select (select deliver p) q) Truth))) Truth Falsity))
(check-sat)
