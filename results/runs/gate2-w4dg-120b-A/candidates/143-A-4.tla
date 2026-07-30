---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
AllPeople == Missionaries \cup Cannibals
BoatCap == 2

VARIABLES boat, bankPop
vars == <<boat, bankPop>>

RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

OccOn(b, k) == Cardinality({p \in bankPop[b] : p \in k})

TypeOK ==
    /\ boat \in Banks
    /\ bankPop \in [Banks -> SUBSET AllPeople]

\* A bank is safe if it has no missionaries, or cannibals do not outnumber
\* them; the puzzle is solved once the east bank is empty.
Solution ==
    /\ \A b \in Banks :
         \/ (OccOn(b, Missionaries) = 0 /\ OccOn(b, Cannibals) > 0)
         \/ (OccOn(b, Missionaries) > 0 /\ OccOn(b, Cannibals) <= OccOn(b, Missionaries))
    /\ OccOn("east", Missionaries) = 0

Init ==
    /\ boat = "east"
    /\ bankPop = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]

\* Passengers is a non-empty subset of the current bank, size bounded by the
\* boat's capacity. The move is only enabled while the resulting configuration
\* is safe on both banks.
Move ==
    /\ \E group \in SUBSET bankPop[boat] :
         /\ group # {}
         /\ SumOf(SIZE, group) <= BoatCap
         /\ LET b2 == IF boat = "east" THEN "west" ELSE "east" IN
              /\ bankPop' = [bankPop EXCEPT ![boat] = @ \ group, ![b2] = @ \cup group]
              /\ boat' = b2

Next == Move

Spec == Init /\ [][Next]_vars

====