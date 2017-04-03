% COMMAND-LINE: --cegqi-si=all --no-dump-synth
% SCRUBBER: sed -e 's/The fact in question: .*$/The fact in question: TERM/'
% EXPECT: (error "A non-linear fact was asserted to arithmetic in a linear logic.
% EXPECT: The fact in question: TERM
% EXPECT: ")
% EXIT: 1
tff(reject_division,conjecture,
    ! [X: $int] :
       ( $quotient(X,X) = 1 )
    ).
