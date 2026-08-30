-------------------------- MODULE MissionariesAndCannibals --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Bank == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, banks

vars == <<boatAt, banks>>

RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

BanksOther(b) == IF b = "east" THEN "west" ELSE "east"

TypeOK ==
  /\ boatAt \in Bank
  /\ banks \in [Bank -> SUBSET People]
  /\ banks.east \cup banks.west = People
  /\ banks.east \cap banks.west = {}

Init ==
  /\ boatAt = "east"
  /\ banks = [b \in Bank |-> IF b = "east" THEN People ELSE {}]

\* A group of one or two people boards the boat on the current bank and crosses.
\* The move is only enabled when the resulting configuration on both banks is safe.
Move ==
  \E G \in SUBSET banks[boatAt] :
    /\ Cardinality(G) \in 1..2
    /\ /\ ~ ( "\emptyset" \in Missionaries /\ G # {}
             /\ banks[boatAt \cap Missionaries] # {}
             /\ SumOf([x \in banks[boatAt] \cap Missionaries |-> 1],
                      banks[boatAt] \cap Missionaries)
                + Cardinality(G \cap Missionaries) > 2 )
       /\ /\ SumOf([x \in banks[BanksOther(boatAt)] \cap Missionaries |-> 1],
                  banks[BanksOther(boatAt)] \cap Missionaries) <=
             SumOf([x \in banks[BanksOther(boatAt)] \cap Cannibals |-> 1],
                  banks[BanksOther(boatAt)] \cap Cannibals)
    /\ banks' = [banks EXCEPT ![boatAt] = @ \ G, ![BanksOther(boatAt)] = @ \cup G]
    /\ boatAt' = BanksOther(boatAt)

Next == Move

\* On every bank, if any missionaries are present, cannibals must not outnumber
\* them. The boat always carries one or two people per crossing.
TypeOK == TypeOK

\* The puzzle is solved when the east bank is empty (everyone has reached the west).
Solution ==
  /\ banks.east = {}
  /\ boatAt \in Bank
  /\ banks \in [Bank -> SUBSET People]

Spec == Init /\ [][Next]_vars
================================================================================