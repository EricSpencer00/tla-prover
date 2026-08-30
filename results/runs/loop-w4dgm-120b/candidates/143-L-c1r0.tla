---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, onBank
vars == <<boatAt, onBank>>

\* SAFETY FACTOR: a bank with no missionaries is always safe (only cannibals there),
\* so the inequality below only ever needs to hold on banks that actually have
\* missionaries on them; it is never violated by a bank of cannibals alone.
BankSafe(b) ==
  \/ onBank[b] \cap Missionaries = {}
  \/ Cardinality(onBank[b] \cap Cannibals)
       <= Cardinality(onBank[b] \cap Missionaries)

TypeOK ==
  /\ boatAt \in Banks
  /\ onBank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
  /\ boatAt = "east"
  /\ onBank = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* Groups are bounded to size one or two here and now; the invariant below
\* repeats the bound as a separate sanity check on the action itself.
Move(g) ==
  /\ Cardinality(g) \in {1, 2}
  /\ g \subseteq onBank[boatAt]
  /\ LET dest == CHOOSE d \in Banks : d # boatAt
     IN /\ \A b \in Banks :
           /\ IF b = boatAt THEN onBank[b] \ g ELSE onBank[b]
           /\ IF b = dest THEN onBank[b] \cup g ELSE onBank[b]
           /\ BankSafe(b)
        /\ boatAt' = dest
        /\ onBank' = [b \in Banks |->
                        IF b = boatAt THEN onBank[b] \ g
                        ELSE IF b = dest THEN onBank[b] \cup g
                        ELSE onBank[b]]
  /\ UNCHANGED <<>>


Next == \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)

Solution == \A b \in Banks : BankSafe(b)

Spec == Init /\ [][Next]_vars
====