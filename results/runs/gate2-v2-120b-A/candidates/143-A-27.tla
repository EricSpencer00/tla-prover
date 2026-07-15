---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)

People == Missionaries \cup Cannibals
Banks  == {"East", "West"}

(* Define a record that maps each bank to the set of people currently there *)
VARIABLES boat, locations

(* ------------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ boat = "East"
    /\ locations = [b \in Banks |-> IF b = "East" THEN People ELSE {}]

(* ------------------------------------------------------------------------- *)
(* Safety condition for a single bank                                        *)
(* ------------------------------------------------------------------------- *)

BankSafe(b) ==
    LET ppl   == locations[b] IN
    LET mCount == Cardinality(ppl \cap Missionaries) IN
    LET cCount == Cardinality(ppl \cap Cannibals) IN
        (mCount = 0) \/ (cCount <= mCount)

(* ------------------------------------------------------------------------- *)
(* Global safety invariant (type correctness and bank safety)               *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
    /\ boat \in Banks
    /\ locations \in [Banks -> SUBSET People]
    /\ \A b \in Banks : locations[b] \subseteq People
    /\ \A p \in People : p \in locations["East"] \/ p \in locations["West"]
    /\ \A b \in Banks : BankSafe(b)

(* ------------------------------------------------------------------------- *)
(* Move action: a group of 1 or 2 people crosses the river                   *)
(* ------------------------------------------------------------------------- *)

Move ==
    \E grp \in SUBSET (locations[boat]) :
        /\ Cardinality(grp) \in 1..2
        /\ LET dest == IF boat = "East" THEN "West" ELSE "East" IN
           /\ \A b \in Banks :
                locations2[b] =
                    IF b = boat   THEN locations[b] \ grp
                    ELSE IF b = dest THEN locations[b] \cup grp
                    ELSE locations[b]
           /\ /\ BankSafe(boat)
              /\ BankSafe(dest)
           /\ boat' = dest
           /\ locations' = locations2

Next == Move

(* ------------------------------------------------------------------------- *)
(* Solution invariant: the west bank eventually contains everyone           *)
(* (the invariant is false while the east bank is non‑empty, causing TLC   *)
(* to report a counterexample that is the solution trace).                 *)
(* ------------------------------------------------------------------------- *)

Solution == locations["East"] = {}

====