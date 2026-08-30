---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}

VARIABLES boatAt, bankOf
vars == <<boatAt, bankOf>>

BankOf(p) == [x \in People |-> IF x \in bankOf[east] THEN "east" ELSE "west"]

RECURSIVE SumSet(_)
SumSet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN 1 + SumSet(S \ {x})

TypeOK ==
  /\ boatAt \in Banks
  /\ bankOf \in [People -> Banks]

\* A solution trace is produced whenever a model checker finds a
\* violation of the "east bank empties" invariant, so the trace is
\* only as short as it needs to be.
SolveGoal == bankOf = [p \in People |-> "west"]

Next ==
  \E g \in [1..2 -> People] :
    LET gSet == {g[1]} \cup (IF g[2] # g[1] THEN {g[2]} ELSE {})
        toBank == IF boatAt = "east" THEN "west" ELSE "east"
        newBankOf == [p \in People |-> IF p \in gSet THEN toBank
                                        ELSE bankOf[p]]
        safe(b) == (bankOf[b] = {}) \/ (SumSet(bankOf[b] \cap Cannibals) <= SumSet(bankOf[b] \cap Missionaries))
    IN
      /\ gSet \subseteq bankOf[boatAt]
      /\ ~bankOf[toBank] = {}
      /\ safe(newBankOf["east"])
      /\ safe(newBankOf["west"])
      /\ bankOf' = newBankOf
      /\ boatAt' = toBank

Init == boatAt = "east" /\ bankOf = [p \in People |-> "east"]

Next == Next \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Safe unless a bank holds missionaries outnumbered by cannibals; a
\* bank of only cannibals is always safe.
TypeOK == TypeOK
Solution == SolveGoal
====