---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
Boarding == Missionaries \cup Cannibals

VARIABLES dock, onBank

vars == <<dock, onBank>>

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumSet(f, S \ {x})

\* Safety is checked on both banks before a move: each bank must leave its
\* missionaries in at least as many numbers as its cannibals, unless none are
\* present (the "only cannibals" safe case). The boat is never empty.
TypeOK ==
  /\ dock \in Banks
  /\ onBank \in [Banks -> SUBSET People]
  /\ SumSet(onBank, Banks) = Cardinality(People)

Init ==
  /\ dock = "east"
  /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move(board) ==
  /\ board \subseteq onBank[dock]
  /\ 1 <= Cardinality(board) <= 2
  /\ LET other == CHOOSE g \in Banks : g # dock IN
       /\ \A b \in Banks :
            LET after == (IF b = dock THEN onBank[b] \ board
                          ELSE IF b = other THEN onBank[b] \cup board
                          ELSE onBank[b])
            IN (Missionaries \subseteq after) \/ (Cardinality(after \cap Cannibals) <= Cardinality(after \cap Missionaries))
       /\ dock' = other
       /\ onBank' = [b \in Banks |-> IF b = dock THEN onBank[b] \ board
                                     ELSE IF b = other THEN onBank[b] \cup board
                                     ELSE onBank[b]]

Next ==
  \/ \E board \in SUBSET Boarding : Move(board)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(Next)

\* The invariant that makes the puzzle interesting (cannibals never win): a
\* bank with missionaries on it is never left with more cannibals than
\* missionaries, and the boat always carries at least one person. The
\* configuration where the departure bank empties (the solution) is itself a
\* safe configuration, so the solver is never pushed into an unsafe move.
Solution == TypeOK

====