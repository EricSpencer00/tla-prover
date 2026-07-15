---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (must be supplied in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N \* number of creatures
CONSTANT M \* total meeting limit
CONSTANT Faded
CONSTANT MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

\* ----------------------------------------------------------------------
\* State variables
\*   col         : mapping each creature to its current color
\*   cnt         : mapping each creature to its meeting participation count
\*   waiting     : either MeetingPlaceEmpty or the id of a creature waiting
\*   totalMeet   : total number of completed meetings so far
\* ----------------------------------------------------------------------
VARIABLES col, cnt, waiting, totalMeet

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK ==
    /\ col \in [Creatures -> Colors]
    /\ cnt \in [Creatures -> Nat]
    /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeet \in Nat

\* Complement function as described in the natural language
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CASE
            /\ {c1, c2} = {"blue", "red"}    -> "yellow"
            /\ {c1, c2} = {"blue", "yellow"} -> "red"
            /\ {c1, c2} = {"red", "yellow"}  -> "blue"
            OTHER                           -> Faded \* should never happen
        ENDCASE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ col = [i \in Creatures |-> CHOOSE c \in {"blue", "red", "yellow"} : TRUE]
    /\ cnt = [i \in Creatures |-> 0]
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeet = 0
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeet < M
    /\ \E i \in Creatures :
        /\ col[i] # Faded
        /\ waiting' = i
        /\ UNCHANGED <<col, cnt, totalMeet>>

FadeOut ==
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeet >= M
    /\ \E i \in Creatures :
        /\ col[i] # Faded
        /\ col' = [col EXCEPT ![i] = Faded]
        /\ UNCHANGED <<cnt, waiting, totalMeet>>

MeetAndMutate ==
    /\ waiting # MeetingPlaceEmpty
    /\ totalMeet < M
    /\ \E i \in Creatures :
        /\ col[i] # Faded
        /\ i # waiting   \* cannot meet itself
        /\ LET newCol == Complement(col[i], col[waiting]) IN
           /\ col' = [col EXCEPT ![i] = newCol,
                              ![waiting] = newCol]
           /\ cnt' = [cnt EXCEPT ![i] = cnt[i] + 1,
                               ![waiting] = cnt[waiting] + 1]
           /\ totalMeet' = totalMeet + 1
           /\ waiting' = MeetingPlaceEmpty
        /\ UNCHANGED <<>>

\* Stuttering step to avoid deadlock when all creatures are faded
Stutter ==
    UNCHANGED <<col, cnt, waiting, totalMeet>>

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<col, cnt, waiting, totalMeet>>

\* ----------------------------------------------------------------------
\* Safety invariant demanded by the description
\* ----------------------------------------------------------------------
SumMet ==
    /\ totalMeet = M => 
        ( /\ \A i \in Creatures : cnt[i] <= M )
        /\ ( /\ totalMeet = M => 
                \A i \in Creatures : col[i] = Faded \/ cnt[i] >= 1 )
    /\ ( /\ totalMeet < M => FALSE) \* vacuous when not at limit
    /\ (totalMeet = M) => ( /\ \A i \in Creatures : cnt[i] >= 0 )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : cnt[i] \in Nat )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : col[i] \in Colors )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : col[i] = Faded \/ cnt[i] >= 1 )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : cnt[i] <= M )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : col[i] # Faded => cnt[i] >= 1 )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : col[i] = Faded => TRUE )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : cnt[i] >= 0 )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : cnt[i] <= M )
    /\ (totalMeet = M) => 
        ( \A i \in Creatures : col[i] \in {"blue","red","yellow",Faded} )
    /\ (totalMeet = M) => 
        ( Sum(cnt) = 2 * M )

\* ----------------------------------------------------------------------
\* OPTIONAL: The configuration file will refer to the invariant SumMet and
\* the type invariant TypeOK.  We expose both as the required identifiers.
\* ----------------------------------------------------------------------
=============================================================================