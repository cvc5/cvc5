; EXPECT: sat
(set-logic ALL)
(declare-const a (Array (_ BitVec 64) (_ BitVec 64)) ) 
(declare-const b (_ BitVec 64) ) 
(assert ( = a ( store a ( bvneg ( bvneg #x1111111111111111 ) ) 
        ( bvadd #x1111111111111111 ( select a #x0000000000000000 ) ) ) ) ) 
( check-sat )
