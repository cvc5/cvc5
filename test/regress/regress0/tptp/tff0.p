% example from the TFF0 paper
% see https://sites.google.com/site/polymorphictptptff/relevant-links/tff-tfa
%
% Status : Theorem
%
tff(student_type,type, ( student: $tType )).
tff(professor_type,type,( professor: $tType )).
tff(course_type,type, ( course: $tType )).
tff(michael_type,type, ( michael: student )).
tff(victor_type,type, ( victor: professor )).
tff(csc410_type,type, ( csc410: course )).
tff(enrolled_type,type, ( enrolled: ( student * course ) > $o )).
tff(teaches_type,type, ( teaches: ( professor * course ) > $o )).
tff(taught_by_type,type,( taughtby: ( student * professor ) > $o )).
tff(coordinator_of_type,type,( coordinatorof: course > professor )).

tff(student_enrolled_axiom,axiom,(
    ! [X: student] : ? [Y: course] : enrolled(X,Y) )).
tff(professor_teaches,axiom,(
    ! [X: professor] : ? [Y: course] : teaches(X,Y) )).
tff(course_enrolled,axiom,(
    ! [X: course] : ? [Y: student] : enrolled(Y,X) )).
tff(course_teaches,axiom,(
    ! [X: course] : ? [Y: professor] : teaches(Y,X) )).
tff(coordinator_teaches,axiom,(
    ! [X: course] : teaches(coordinatorof(X),X) )).
tff(student_enrolled_taught,axiom,(
    ! [X: student,Y: course] :
      ( enrolled(X,Y)
     => ! [Z: professor] : ( teaches(Z,Y) => taughtby(X,Z) ) ) )).
tff(michael_enrolled_csc410_axiom,axiom,(
    enrolled(michael,csc410) )).
tff(victor_coordinator_csc410_axiom,axiom,(
    coordinatorof(csc410) = victor )).

tff(teaching_conjecture,conjecture,(
    taughtby(michael,victor) )).
