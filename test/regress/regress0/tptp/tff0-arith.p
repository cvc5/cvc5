% example from the TFF0 paper
% see https://sites.google.com/site/polymorphictptptff/relevant-links/tff-tfa
%
% Status : Theorem
%
tff(list_type,type, ( list: $tType )).
tff(nil_type,type, ( nil: list )).
tff(mycons_type,type,( mycons: ( $int * list ) > list )).
tff(sorted_type,type,( fib_sorted: list > $o )).

tff(empty_fib_sorted,axiom,(
    fib_sorted(nil) )).
tff(single_is_fib_sorted,axiom,(
    ! [X: $int] : fib_sorted(mycons(X,nil)) )).
tff(double_is_fib_sorted_if_ordered,axiom,(
    ! [X: $int,Y: $int] :
      ( $less(X,Y)
     => fib_sorted(mycons(X,mycons(Y,nil))) ) )).
tff(recursive_fib_sort,axiom,(
    ! [X: $int,Y: $int,Z: $int,R: list] :
      ( ( $less(X,Y)
        & $greatereq(Z,$sum(X,Y))
        & fib_sorted(mycons(Y,mycons(Z,R))) )
     => fib_sorted(mycons(X,mycons(Y,mycons(Z,R)))) ) )).

tff(check_list,conjecture,(
    fib_sorted(mycons(1,mycons(2,mycons(4,nil)))) )).
