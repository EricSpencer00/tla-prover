---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES people, mall, total

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Complement rule for two (non‑faded) colors
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE col \in {"blue", "red", "yellow"} :
      /\ col # c1
      /\ col # c2

\* Sum of individual meeting counts
SumCounts == 
  \* The sum of the 'cnt' field over all creatures
  +/\[i \in 1..N |-> people[i].cnt]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ people = [i \in 1..N |-> 
        [color |-> (CHOOSE c \in NonFadedColors : TRUE),
         cnt   |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ c \in 1..N
  /\ people[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<people, total>>

FadeOut(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ c \in 1..N
  /\ people[c].color # Faded
  /\ people' = [people EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, total>>

MeetAndMutate(c2) ==
  /\ mall \in 1..N                \* there is a waiting creature c1 = mall
  /\ total < M
  /\ c2 \in 1..N
  /\ c2 # mall
  /\ people[mall].color # Faded
  /\ people[c2].color # Faded
  /\ LET newcol == Complement(people[mall].color, people[c2].color) IN
        people' = [people EXCEPT 
                     ![mall].color = newcol,
                     ![mall].cnt   = @ + 1,
                     ![c2].color   = newcol,
                     ![c2].cnt     = @ + 1]
  /\ total' = total + 1
  /\ mall' = MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E c \in 1..N: EnterEmpty(c)
  \/ \E c \in 1..N: FadeOut(c)
  \/ \E c \in 1..N: MeetAndMutate(c)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<people, mall, total>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ people \in [1..N -> [color : Colors, cnt : Nat]]
  /\ mall \in (MeetingPlaceEmpty \cup 1..N)
  /\ total \in Nat

\* ----------------------------------------------------------------------
\* Safety property: sum of meeting counts when the limit is reached
\* ----------------------------------------------------------------------
SumMet ==
  (total = M) => (SumCounts = 2 * M)

====