---------------------------- MODULE W4Od2m8p2t4 ---------------------------
EXTENDS Naturals

CONSTANTS NumBays, NumRobots, NorthBays, MinLimit, MaxLimit, DeckSize

Bays == 1 .. NumBays
Robots == 1 .. NumRobots
Nobody == 0
Aisles == {"north", "south"}
AisleOf(b) == IF b \in NorthBays THEN "north" ELSE "south"

VARIABLES shelf, deck, aisleHold, bayHold, limit
vars == <<shelf, deck, aisleHold, bayHold, limit>>

RECURSIVE ShelfUpto(_)
ShelfUpto(k) == IF k = 0 THEN 0 ELSE shelf[k] + ShelfUpto(k - 1)

RECURSIVE DeckUpto(_)
DeckUpto(k) == IF k = 0 THEN 0 ELSE deck[k] + DeckUpto(k - 1)

TypeOK ==
  /\ shelf \in [Bays -> 0 .. MaxLimit]
  /\ deck \in [Robots -> 0 .. DeckSize]
  /\ aisleHold \in [Aisles -> Robots \cup {Nobody}]
  /\ bayHold \in [Bays -> Robots \cup {Nobody}]
  /\ limit \in [Bays -> MinLimit .. MaxLimit]

Init ==
  /\ shelf = [b \in Bays |-> 1]
  /\ deck = [r \in Robots |-> 0]
  /\ aisleHold = [a \in Aisles |-> Nobody]
  /\ bayHold = [b \in Bays |-> Nobody]
  /\ limit = [b \in Bays |-> MaxLimit]

TakeAisle(r, a) ==
  /\ aisleHold[a] = Nobody
  /\ aisleHold' = [aisleHold EXCEPT ![a] = r]
  /\ UNCHANGED <<shelf, deck, bayHold, limit>>

\* Fine hold is only reachable from underneath a coarse hold by the same robot.
TakeBay(r, b) ==
  /\ bayHold[b] = Nobody
  /\ aisleHold[AisleOf(b)] = r
  /\ bayHold' = [bayHold EXCEPT ![b] = r]
  /\ UNCHANGED <<shelf, deck, aisleHold, limit>>

Pick(r, b) ==
  /\ bayHold[b] = r
  /\ shelf[b] > 0
  /\ deck[r] < DeckSize
  /\ shelf' = [shelf EXCEPT ![b] = shelf[b] - 1]
  /\ deck' = [deck EXCEPT ![r] = deck[r] + 1]
  /\ UNCHANGED <<aisleHold, bayHold, limit>>

Place(r, b) ==
  /\ bayHold[b] = r
  /\ deck[r] > 0
  /\ shelf[b] < limit[b]
  /\ shelf' = [shelf EXCEPT ![b] = shelf[b] + 1]
  /\ deck' = [deck EXCEPT ![r] = deck[r] - 1]
  /\ UNCHANGED <<aisleHold, bayHold, limit>>

\* Rack beams move mid-shift, but never below what is already on the shelf.
Restripe(r, b, c) ==
  /\ bayHold[b] = r
  /\ c \in MinLimit .. MaxLimit
  /\ c >= shelf[b]
  /\ limit' = [limit EXCEPT ![b] = c]
  /\ UNCHANGED <<shelf, deck, aisleHold, bayHold>>

DropBay(r, b) ==
  /\ bayHold[b] = r
  /\ bayHold' = [bayHold EXCEPT ![b] = Nobody]
  /\ UNCHANGED <<shelf, deck, aisleHold, limit>>

DropAisle(r, a) ==
  /\ aisleHold[a] = r
  /\ \A b \in Bays : AisleOf(b) = a => bayHold[b] # r
  /\ aisleHold' = [aisleHold EXCEPT ![a] = Nobody]
  /\ UNCHANGED <<shelf, deck, bayHold, limit>>

Next ==
  \/ \E r \in Robots, a \in Aisles : TakeAisle(r, a)
  \/ \E r \in Robots, b \in Bays : TakeBay(r, b)
  \/ \E r \in Robots, b \in Bays : Pick(r, b)
  \/ \E r \in Robots, b \in Bays : Place(r, b)
  \/ \E r \in Robots, b \in Bays, c \in MinLimit .. MaxLimit : Restripe(r, b, c)
  \/ \E r \in Robots, b \in Bays : DropBay(r, b)
  \/ \E r \in Robots, a \in Aisles : DropAisle(r, a)

Spec == Init /\ [][Next]_vars

\* Nightly count: shelves plus decks is a building-wide constant.
StockCountHolds ==
  ShelfUpto(NumBays) + DeckUpto(NumRobots) = NumBays
===========================================================================