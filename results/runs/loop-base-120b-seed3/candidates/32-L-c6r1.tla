---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets of colors
\* ----------------------------------------------------------------------
ColorSet == {"blue", "red", "yellow"}
Colors   == ColorSet \cup {Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES creatures, place, total

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE c \in ColorSet :
            /\ c # c1
            /\ c # c2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ place = MeetingPlaceEmpty
  /\ total = 0
  /\ \E col \in [1..N -> ColorSet] :
        creatures = [i \in 1..N |-> [color |-> col[i], count |-> 0]]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ creatures[i].color # Faded
        /\ place' = i
        /\ UNCHANGED <<creatures, total>>

Fade ==
  /\ place = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
        /\ creatures[i].color # Faded
        /\ creatures' = [creatures EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<place, total>>

Meet ==
  /\ place \in 1..N                \* someone is waiting
  /\ total < M
  /\ \E i \in 1..N :
        /\ i # place
        /\ creatures[i].color # Faded
        /\ creatures[place].color # Faded
        /\ LET newColor == Complement(creatures[i].color,
                                      creatures[place].color) IN
           /\ creatures' = [creatures EXCEPT
                              ![i]   = [color |-> newColor,
                                        count |-> @.count + 1],
                              ![place] = [color |-> newColor,
                                         count |-> @.count + 1]]
        /\ total' = total + 1
        /\ place' = MeetingPlaceEmpty

Next == \/ Enter \/ Fade \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<creatures, place, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ place \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat
  /\ creatures \in [1..N -> [color : Colors, count : Nat]]

SumCounts == \Sum i \in 1..N: creatures[i].count

SumMet == (total = M) => (SumCounts = 2 * M)

====