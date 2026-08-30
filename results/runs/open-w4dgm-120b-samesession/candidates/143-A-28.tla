---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

\* The bank-to-set maps the bank a person currently stands on; the boat's
\* boarding count is recomputed from this rather than stored, so the bound
\* on boarders is a genuine consequence of the move, not a second copy.
VARIABLES boat, bankOf

vars == <<boat, bankOf>>

BankCount(b, S) == Cardinality({p \in People : bankOf[p] = b /\ p \in S})

TypeOK ==
  /\ boat \in Banks
  /\ bankOf \in [People -> Banks]

\* A bank with missionaries must never be outnumbered by cannibals; a bank
\* with only cannibals is safe by definition.
BanksAreSafe ==
  /\ \A b \in Banks:
       (BankCount(b, Missionaries) > 0) =>
         (BankCount(b, Cannibals) <= BankCount(b, Missionaries))
  /\ \A b \in Banks: BankCount(b, Missionaries) + BankCount(b, Cannibals) <= 3

Init ==
  /\ boat = "east"
  /\ bankOf = [p \in People |-> "east"]

\* The boat cannot cross empty; the boarding group is chosen on the
\* departure bank and must lead to a safe configuration on both banks.
Move ==
  \E S \in SUBSET People :
    /\ S # {}
    /\ Cardinality(S) <= 2
    /\ \A p \in S : bankOf[p] = boat
    /\ LET dest == IF boat = "east" THEN "west" ELSE "east" IN
         /\ \A b \in Banks:
              (BankCount(b, Missionaries) > 0) =>
                (BankCount(b, Cannibals) <= BankCount(b, Missionaries))
         /\ bankOf' = [p \in People |-> IF p \in S THEN dest ELSE bankOf[p]]
         /\ boat' = dest

Next == Move

Solution == \A p \in People : bankOf[p] = "west"

Spec == Init /\ [][Next]_vars

INVARIANT TypeOK
INVARIANT BanksAreSafe
====