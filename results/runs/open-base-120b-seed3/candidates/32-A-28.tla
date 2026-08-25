---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Creatures == 1..N
BasicColors == {"blue", "red", "yellow"}
Colors == BasicColors \cup {Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES cstate, mall, total

\* ----------------------------------------------------------------------
\* Complement rule for colors
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE IF (c1 = "blue"  /\ c2 = "red")    \/ (c1 = "red"    /\ c2 = "blue")    THEN "yellow"
  ELSE IF (c1 = "blue"  /\ c2 = "yellow")\/ (c1 = "yellow" /\ c2 = "blue")   THEN "red"
  ELSE IF (c1 = "red"   /\ c2 = "yellow")\/ (c1 = "yellow" /\ c2 = "red")    THEN "blue"
  ELSE Faded   \* should never be reached for valid inputs

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ cstate \in [Creatures -> [color : BasicColors, count : Nat]]
  /\ \A i \in Creatures : cstate[i].count = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ i \in Creatures
  /\ cstate[i].color # Faded
  /\ mall' = i
  /\ UNCHANGED <<cstate, total>>

Fade(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ i \in Creatures
  /\ cstate[i].color # Faded
  /\ cstate' = [cstate EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<mall, total>>

Meet(i) ==
  /\ mall # MeetingPlaceEmpty
  /\ i \in Creatures
  /\ i # mall
  /\ cstate[i].color # Faded
  /\ cstate[mall].color # Faded
  /\ total < M
  /\ LET newcol == Complement(cstate[i].color, cstate[mall].color) IN
        /\ cstate' = [cstate EXCEPT
                       ![i].color   = newcol,
                       ![i].count   = @ + 1,
                       ![mall].color = newcol,
                       ![mall].count = @ + 1]
  /\ total' = total + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E i \in Creatures : Enter(i)
  \/ \E i \in Creatures : Fade(i)
  \/ \E i \in Creatures : Meet(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<cstate, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ cstate \in [Creatures -> [color : Colors, count : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  (total = M) => (\Sum i \in Creatures : cstate[i].count = 2 * M)

\* ----------------------------------------------------------------------
\* Exported identifiers (as required by the .cfg file)
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
\* INVARIANTS
\* (the cfg file will refer to the names below)
\* ----------------------------------------------------------------------
\* SPECIFICATION
\*   Spec
\* INVARIANTS
\*   TypeOK
\*   SumMet
=============================================================================