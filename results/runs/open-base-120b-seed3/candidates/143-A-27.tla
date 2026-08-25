---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(* Derived constants *)
People == Missionaries \cup Cannibals

(* ---------------------------------------------------------------------- *)
(* Banks *)
East == "East"
West == "West"
Banks == {East, West}

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES boatBank, bank

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

Opposite(b) == IF b = East THEN West ELSE East

IsSafe(bset) ==
  LET m == bset \cap Missionaries
      c == bset \cap Cannibals
  IN (m = {}) \/ (Cardinality(c) <= Cardinality(m))

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ boatBank = East
  /\ bank = [b \in Banks |-> IF b = East THEN People ELSE {}]

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
  \E passengers \in SUBSET People :
    /\ passengers # {}                                   \* at least one person
    /\ Cardinality(passengers) \in 1..2                  \* one or two people
    /\ passengers \subseteq bank[boatBank]               \* they board where the boat is
    /\ LET newBank == 
          [b \in Banks |-> 
             IF b = boatBank 
                THEN bank[b] \ SetMinus passengers 
                ELSE bank[b] \cup passengers] 
       IN 
         /\ IsSafe(newBank[East])
         /\ IsSafe(newBank[West])
         /\ boatBank' = Opposite(boatBank)
         /\ bank' = newBank

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
  /\ boatBank \in Banks
  /\ bank \in [Banks -> SUBSET People]
  /\ \A b \in Banks : IsSafe(bank[b])
  /\ (bank[East] \cup bank[West]) = People
  /\ bank[East] \cap bank[West] = {}

Solution ==
  bank[East] = {}

====