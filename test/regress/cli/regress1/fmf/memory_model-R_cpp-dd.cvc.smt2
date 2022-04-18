; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(set-option :produce-models true)
(set-option :fmf-bound true)
(declare-datatypes ((MOPERATION 0)) (((R) (W) (M))))
(declare-datatypes ((ORDER 0)) (((I) (SC) (U))))
(declare-datatypes ((ATOM 0)) (((AT) (NA))))
(declare-datatypes ((BINT 0)) (((I0) (I1) (I2) (I3))))
(declare-datatypes ((TEAR_TYPE 0)) (((TEAR_TRUE) (TEAR_FALSE))))
(declare-sort SDBLOCK_TYPE 0)
(declare-sort VALUE_TYPE 0)

(declare-datatypes ((|__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE| 0)) (((|__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE_ctor| (O MOPERATION) (T TEAR_TYPE) (RR ORDER) (A ATOM) (B SDBLOCK_TYPE) (M (Set BINT)) (V VALUE_TYPE)))))


(declare-datatypes ((|__cvc5_record_E_(Set ___cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE_)_PO_(Relation ___cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE_ ___cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE_)| 0)) (((|__cvc5_record_E_(Set ___cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE_)_PO_(Relation ___cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE_ ___cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE_)_ctor| (E (Set |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE|)) (PO (Relation |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE| |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE|))))))

(declare-fun m1 () SDBLOCK_TYPE)
(declare-fun ow1 () |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE|)
(declare-fun or2 () |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE|)
(declare-fun v1 () VALUE_TYPE)
(declare-fun v2 () VALUE_TYPE)
(assert (and (and (and (and (and (and (= (O ow1) W) (= (T ow1) TEAR_FALSE)) (= (RR ow1) U)) (= (A ow1) NA)) (= (B ow1) m1)) (= (M ow1) (set.singleton I0))) (= (V ow1) v1)))
(assert (and (and (and (and (and (and (= (O or2) R) (= (T or2) TEAR_FALSE)) (= (RR or2) U)) (= (A or2) NA)) (= (B or2) m1)) (= (M or2) (set.singleton I0))) (= (V or2) v2)))
(declare-fun ev_set () (Set |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE|))
(assert (= ev_set (set.union (set.singleton ow1) (set.singleton or2))))
(declare-fun RF () (Relation |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE| |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE|))
(assert (forall ((r |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE|) (w |__cvc5_record_O_MOPERATION_T_TEAR_TYPE_R_ORDER_A_ATOM_B_SDBLOCK_TYPE_M_(Set BINT)_V_VALUE_TYPE|)) (=> (and (set.member r ev_set) (set.member w ev_set)) (= (set.member (tuple r w) RF) (and (= (O r) R) (= (O w) W))))))
(check-sat)
