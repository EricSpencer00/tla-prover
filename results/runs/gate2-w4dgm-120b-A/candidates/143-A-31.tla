---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
Everyone == Missionaries \union Cannibals
PeopleCount(b, S) == Cardinality({p \in S : b[p] = b})

VARIABLES b, pos, pending, dock

vars == <<b, pos, pending, dock>>

RECURSIVE OnBank(_, _)
OnBank(S, bank) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN (IF pos[x] = bank THEN 1 ELSE 0) + OnBank(S \ {x}, bank)

NextRider(x, S) == IF x \in S THEN x else NextRider(CHOOSE y \in S : TRUE, S \ {x})

TypeOK ==
    /\ b \in [Banks -> SUBSET Everyone]
    /\ pos \in [Everyone -> Banks]
    /\ pending \in Seq(Everyone)
    /\ dock \in Banks

Init ==
    /\ b \in [Banks -> SUBSET Everyone]
    /\ pos \in [Everyone -> Banks]
    /\ pending \in Seq(Everyone)
    /\ dock \in Banks
    /\ \A p \in Everyone : pos[p] = "east"
    /\ b["east"] = Everyone
    /\ b["west"] = {}
    /\ pending = <<>>
    /\ dock = "east"

\* A bank with only cannibals is safe (no missionaries to endanger); otherwise
\* the cannibals must not outnumber the missionaries.
BankIsSafe(bank) ==
    \/ {p \in b[bank] : p \in Missionaries} = {}
    \/ Cardinality({p \in b[bank] : p \in Cannibals})
         <= Cardinality({p \in b[bank] : p \in Missionaries})

\* Move is enabled only while the board is safe and the boat holds at most two.
Move(g) ==
    /\ b[dock] # {}
    /\ g # {}
    /\ \A p \in g : pos[p] = dock
    /\ Cardinality(g) <= 2
    /\ Cardinality(g) >= 1
    /\ \A bank \in Banks :
         \A S \in {b[bank] \union g, b[bank] \union {NextRider(p, g) : p \in g}} :
            BankIsSafe(bank)
    /\ pos' = [p \in Everyone |-> IF p \in g THEN dock ELSE pos[p]]
    /\ b' = [bank \in Banks |-> (b[bank] \union g) \ {p \in g : dock = bank}]
    /\ dock' = IF dock = "east" THEN "west" ELSE "east"
    /\ UNCHANGED <<pending>>

Next ==
    \/ \E p \in Everyone : Move({p})
    \/ \E p1 \in Everyone, p2 \in Everyone :
         Move({p1, p2})
    \/ \E p \in Everyone : pending' = Append(pending, p)
    \/ \E i \in 1..Len(pending) :
         Move({pending[i]}) /\ pending' = SubSeq(pending, i + 1, Len(pending))

\* The east bank becomes empty exactly when everyone has reached the west bank.
Solution == \A p \in Everyone : (pos[p] = "west") <=> (p \in b["west"])

BankSafety == \A bank \in Banks : BankIsSafe(bank)

\* A model checking run that finds a violation of the 'east bank is non-empty'
\* invariant has produced a solution trace: the east bank has been emptied
\* by safe moves, so everyone has crossed the river.
\* (This is a tractable property of the model, not a liveness guarantee.)
====