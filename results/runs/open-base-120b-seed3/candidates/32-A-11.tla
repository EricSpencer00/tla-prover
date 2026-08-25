---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets and derived constants
\* ----------------------------------------------------------------------
Creatures == 1..N
Colors    == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES col, cnt, mall, total

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in Colors : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ col \in [Creatures -> Colors]               \* each creature gets a non‑faded color
  /\ cnt = [i \in Creatures |-> 0]               \* zero meetings for everyone
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ i \in Creatures
  /\ col[i] # Faded
  /\ mall' = i
  /\ UNCHANGED <<col, cnt, total>>

Fade(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ i \in Creatures
  /\ col[i] # Faded
  /\ col' = [col EXCEPT ![i] = Faded]
  /\ UNCHANGED <<cnt, mall, total>>

Meet(i) ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ i \in Creatures
  /\ i # mall
  /\ col[i]    # Faded
  /\ col[mall] # Faded
  LET newCol == Complement(col[i], col[mall]) IN
    /\ col' = [col EXCEPT ![i] = newCol, ![mall] = newCol]
    /\ cnt' = [cnt EXCEPT ![i] = @ + 1, ![mall] = @ + 1]
    /\ total' = total + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E i \in Creatures : Enter(i)
  \/ \E i \in Creatures : Fade(i)
  \/ \E i \in Creatures : Meet(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<col, cnt, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ col \in [Creatures -> (Colors \cup {Faded})]
  /\ cnt \in [Creatures -> Nat]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

SumMet ==
  (total = M) => (∑ i \in Creatures : cnt[i]) = 2 * M

=============================================================================