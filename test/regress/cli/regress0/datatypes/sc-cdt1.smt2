(set-logic ALL)
(set-info :status sat)
(declare-sort term 0)
(declare-codatatypes ((llist_tree 0) (tree 0)) (
    ( (lnil_tree )
        (lcons_tree (_select_llist_tree_0 tree)
        (_select_llist_tree_1 llist_tree)))
    ((leaf (_select_tree_0 term))
        (node (_select_tree_1 llist_tree)))
))
(declare-fun nun_sk_2 () term)
(declare-fun nun_sk_1 () term)
(declare-fun nun_sk_0 () tree)
(assert
    (= nun_sk_0
        (node
         (lcons_tree (leaf nun_sk_1)
          (lcons_tree (leaf nun_sk_2) (lcons_tree nun_sk_0 lnil_tree))))))
(check-sat)
