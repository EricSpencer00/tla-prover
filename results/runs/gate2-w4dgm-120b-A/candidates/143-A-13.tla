---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES side, occupants, boatLoad, boatSide

vars == <<side, occupants, boatLoad, boatSide>>

\* occupants: who is on each river bank. boatLoad: who is currently in the boat.
\* boatSide: the bank the boat is docked at (the side it will leave from).
TypeOK ==
    /\ side \in Banks
    /\ occupants \in [Banks -> SUBSET People]
    /\ boatLoad \subseteq People
    /\ boatSide \in Banks

Init ==
    /\ side = "west"
    /\ occupants = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]
    /\ boatLoad = {}
    /\ boatSide = "east"

\* Safety: a bank with missionaries must not have more cannibals than missionaries.
BankSafe(b) ==
    LET m == Cardinality(Missionaries \cap occupants[b])
        c == Cardinality(Cannibals \cap occupants[b])
    IN m = 0 \/ c <= m

\* Everybody crossing is in the boat; the rest stay put on the departure bank.
Move ==
    /\ boatLoad # {}
    /\ Cardinality(boatLoad) <= 2
    /\ LET depart == occupants[side] \ boatLoad
           arrive == occupants[side] \cup boatLoad
       IN /\ side' = IF side = "west" THEN "east" ELSE "west"
          /\ occupants' = [occupants EXCEPT ![side] = depart, ![IF side = "west" THEN "east" ELSE "west"] = arrive]
    /\ boatSide' = IF side = "west" THEN "east" ELSE "west"
    /\ boatLoad' = {}

Board(p) ==
    /\ p \in occupants[side]
    /\ boatLoad = {}
    /\ Cardinality(occupants[side]) > 1
    /\ boatLoad' = {p}
    /\ UNCHANGED <<side, occupants, boatSide>>

BoardSecond(p) ==
    /\ boatLoad # {}
    /\ Cardinality(boatLoad) = 1
    /\ p \in occupants[side]
    /\ p \notin boatLoad
    /\ boatLoad' = boatLoad \cup {p}
    /\ UNCHANGED <<side, occupants, boatSide>>

BoardAny == \E p \in People : Board(p) \/ BoardSecond(p)

Next == Move \/ BoardAny

Spec == Init /\ [][Next]_vars

\* The puzzle is solved only when the departure bank is empty (all crossed).
Solution == occupants["east"] = {}

\* TypeOK is a structural check; the no-outnumbering rule is the substantive safety property.
\* Both are required here because a spec with no invariants at all would pass vacuously.
TypeOK == TypeOK
BankSafety == \A b \in Banks : BankSafe(b)
====