---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES col, cnt, mall, total

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Creatures == 1..N
Colors   == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CASE
      (c1 = "blue" /\ c2 = "red")   \/ (c1 = "red"   /\ c2 = "blue")   -> "yellow"
    [] (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") -> "red"
    [] (c1 = "red" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red")   -> "blue"
    [] OTHER -> Faded
    ENDCASE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ col \in [Creatures -> NonFadedColors]
  /\ cnt = [i \in Creatures |-> 0]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(i) ==
  /\ i \in Creatures
  /\ col[i] # Faded
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ mall' = i
  /\ UNCHANGED <<col, cnt, total>>

Fade(i) ==
  /\ i \in Creatures
  /\ col[i] # Faded
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ col' = [col EXCEPT ![i] = Faded]
  /\ UNCHANGED <<cnt, mall, total>>

Meet(j) ==
  /\ j \in Creatures
  /\ mall \in Creatures
  /\ j # mall
  /\ total < M
  /\ col[j] # Faded
  /\ col[mall] # Faded
  LET newc == Complement(col[j], col[mall]) IN
    /\ col' = [col EXCEPT ![j] = newc, ![mall] = newc]
    /\ cnt' = [cnt EXCEPT ![j] = @ + 1, ![mall] = @ + 1]
    /\ total' = total + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E i \in Creatures: Enter(i)
  \/ \E i \in Creatures: Fade(i)
  \/ \E j \in Creatures: Meet(j)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<col, cnt, mall, total>>

Spec == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ col \in [Creatures -> Colors]
  /\ cnt \in [Creatures -> Nat]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

SumMet ==
  total = M => (∑ i \in Creatures: cnt[i]) = 2 * M

\* ----------------------------------------------------------------------
\* The set of invariants to be checked
\* ----------------------------------------------------------------------
\* (TLC will be instructed via the .cfg file to check these)
\* INVARIANT TypeOK, SumMet

====