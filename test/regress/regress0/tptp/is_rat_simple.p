% states that all reals are not rational (countersatisfiable)
% Status   : CounterSatisfiable
%------------------------------------------------------------------------------
tff(the,conjecture,(
    ! [X: $real] :
      ~ $is_rat(X) ) ).

%------------------------------------------------------------------------------
