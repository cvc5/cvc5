; COMMAND-LINE: --bv-solver=bitblast
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-logic QF_BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 59))
(declare-fun b () (_ BitVec 46))
(assert (bvule (bvmul a #b10110010010100110100010010000100101001100001010010001100101) (concat (bvshl b #b1111110001100111010100001110111111110101011100) #b0001101010101)))
(check-sat)
