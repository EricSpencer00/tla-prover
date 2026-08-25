---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* --------------------------------------------------------------------- *)
(* Derived constants *)
People   == Missionaries \cup Cannibals
BankIds  == {"East", "West"}

(* --------------------------------------------------------------------- *)
(* State variables *)
VARIABLES BoatPos, Bank

(* --------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
    /\ BoatPos \in BankIds
    /\ Bank \in [BankIds -> SUBSET People]
    /\ UNION Bank = People
    /\ \A b1, b2 \in BankIds :
          (b1 # b2) => (Bank[b1] \cap Bank[b2] = {})

(* --------------------------------------------------------------------- *)
(* Helper definitions *)
MissionariesOn(b) == Cardinality( Bank[b] \cap Missionaries )
CannibalsOn(b)    == Cardinality( Bank[b] \cap Cannibals )

SafeBank(b) ==
    \/ MissionariesOn(b) = 0
    \/ CannibalsOn(b) <= MissionariesOn(b)

Safe == \A b \in BankIds : SafeBank(b)

Other(b) == IF b = "East" THEN "West" ELSE "East"

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ BoatPos = "East"
    /\ Bank = [b \in BankIds |-> IF b = "East" THEN People ELSE {}]

(* --------------------------------------------------------------------- *)
(* Move action: transport 1 or 2 persons, never empty *)
Move ==
    \E grp \subseteq Bank[BoatPos] :
        /\ Cardinality(grp) \in 1..2
        /\ LET dest == Other(BoatPos) IN
               /\ BoatPos' = dest
               /\ Bank' = [Bank EXCEPT
                            ![BoatPos] = Bank[BoatPos] \ grp,
                            ![dest]   = Bank[dest] \cup grp]
               /\ Safe'

Next == Move

(* --------------------------------------------------------------------- *)
(* Solution invariant: east bank empty (all have reached west) *)
Solution == Bank["East"] = {}

(* --------------------------------------------------------------------- *)
(* (Optional) full specification *)
Spec == Init /\ [][Next]_<<BoatPos, Bank>>

====