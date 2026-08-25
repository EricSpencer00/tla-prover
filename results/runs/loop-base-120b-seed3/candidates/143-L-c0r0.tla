---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(*  Derived sets *)
People == Missionaries \cup Cannibals
Banks  == {"East", "West"}

(* ---------------------------------------------------------------------- *)
(*  State variables *)
VARIABLES boatPos, bank

(* ---------------------------------------------------------------------- *)
(*  Helper definitions *)

Cardinality(S) == IF S = {} THEN 0 ELSE Len(Seq(S))

MissionariesOn(b) == { p \in b : p \in Missionaries }
CannibalsOn(b)   == { p \in b : p \in Cannibals }

SafeBank(b) ==
  LET m == Cardinality(MissionariesOn(b))
      c == Cardinality(CannibalsOn(b))
  IN  (m = 0) \/ (c <= m)

Safe == \A b \in Banks : SafeBank(bank[b])

AllPeopleOnEast ==
  bank["East"] = People /\ bank["West"] = {}

(* ---------------------------------------------------------------------- *)
(*  Initial state *)

Init ==
  /\ boatPos = "East"
  /\ bank = [b \in Banks |-> IF b = "East" THEN People ELSE {}]

(* ---------------------------------------------------------------------- *)
(*  Move action *)

Move ==
  \E grp \in SUBSET bank[boatPos] :
    /\ Cardinality(grp) \in 1..2
    /\ LET newPos == IF boatPos = "East" THEN "West" ELSE "East"
           newBank == [b \in Banks |-> 
                         IF b = boatPos THEN bank[b] \ grp
                         ELSE IF b = newPos THEN bank[b] \cup grp
                         ELSE bank[b]]
       IN
          /\ SafeBank(newBank["East"])
          /\ SafeBank(newBank["West"])
          /\ boatPos' = newPos
          /\ bank'    = newBank

Next == Move

(* ---------------------------------------------------------------------- *)
(*  Type correctness invariant *)

TypeOK ==
  /\ boatPos \in Banks
  /\ bank \in [Banks -> SUBSET People]
  /\ \A p \in People : (p \in bank["East"]) \/ (p \in bank["West"])
  /\ (bank["East"] \cap bank["West"]) = {}

(* ---------------------------------------------------------------------- *)
(*  Solution invariant *)

Solution == bank["East"] = {}

(* ---------------------------------------------------------------------- *)
(*  Specification (optional) *)

Spec == Init /\ [][Next]_<<boatPos, bank>>

====