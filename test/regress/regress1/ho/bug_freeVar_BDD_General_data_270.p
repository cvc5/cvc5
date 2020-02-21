% COMMAND-LINE: --uf-ho --finite-model-find
% EXPECT: % SZS status Satisfiable for bug_freeVar_BDD_General_data_270

thf(ty_n_t__Nat__Onat, type,
    nat : $tType).

thf(sy_c_Orderings_Oord__class_Oless__eq_001t__Nat__Onat, type,
    ord_less_eq_nat : nat > nat > $o).

thf(fact_76_eq__iff, axiom,
    (((^[Y3 : nat]: (^[Z2 : nat]: (Y3 = Z2))) = (^[X4 : nat]: (^[Y4 : nat]: (((ord_less_eq_nat @ X4 @ Y4)) & ((ord_less_eq_nat @ Y4 @ X4)))))))). % eq_iff
