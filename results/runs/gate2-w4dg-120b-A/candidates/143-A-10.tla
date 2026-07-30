---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
\* BankOf[p] is the current bank where person p resides; MissionariesOn(b)
\* and CannibalsOn(b) count missionaries/cannibals on bank b using that.
VARIABLES BoatAt, BankOf

TypeOK ==
    /\ BoatAt \in Banks
    /\ BankOf \in [People -> Banks]
    /\ Cardinality({p \in People : BankOf[p] = "east"}) <= 6
    /\ Cardinality({p \in People : BankOf[p] = "west"}) <= 6

MissionariesOn(b) == Cardinality({p \in Missionaries : BankOf[p] = b})
CannibalsOn(b) == Cardinality({p \in Cannibals : BankOf[p] = b})
BankSafe(b) == MissionariesOn(b) = 0 \/ CannibalsOn(b) <= MissionariesOn(b)

Init ==
    /\ BoatAt = "east"
    /\ BankOf = [p \in People |-> "east"]

\* A move takes exactly one or two people from the boat's current bank to the
\* other bank; the resulting banks must both satisfy the safety rule.
\* Varying the cardinality directly forces the boat to carry at least one and
\* at most two people per crossing -- the other safety property.
Move ==
    /\ \E S \in (SUBSET People) :
         /\ S # {}
         /\ Cardinality(S) <= 2
         /\ \A p \in S : BankOf[p] = BoatAt
         /\ LET b == IF BoatAt = "east" THEN "west" ELSE "east" IN
              /\ \A p \in S : BankOf' = [BankOf EXCEPT ![p] = b]
              /\ /\ BankSafe("east")
                 /\ BankSafe("west")
              /\ BoatAt' = b
    /\ UNCHANGED << >>

Next == Move

\* The solution is that everyone has left the east bank; both banks' safety
\* rule is still in force all the way to that final state.
Solution ==
    /\ (\A p \in Missionaries : BankOf[p] = "west")
    /\ (\A p \in Cannibals : BankOf[p] = "west")
    /\ BankSafe("west")
    /\ BoatAt = "west"

Spec == Init /\ [][Next]_<<BoatAt, BankOf>>

====