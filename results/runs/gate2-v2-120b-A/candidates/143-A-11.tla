---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(*   Derived sets and helper definitions                                 *)
(* ---------------------------------------------------------------------- *)

People == Missionaries \cup Cannibals

Banks == {"East", "West"}

(* Ensure the constants are non‑empty sets of equal size as required by the
   description.  The actual elements are supplied by the .cfg file. *)
TypeOKConsts ==
    /\ Missionaries /= {}
    /\ Cannibals    /= {}
    /\ Missionaries # Cannibals
    /\ Cardinality(Missionaries) = Cardinality(Cannibals)

(* ---------------------------------------------------------------------- *)
(*   Variables                                                            *)
(* ---------------------------------------------------------------------- *)

VARIABLES boatDocked, peopleOnBank

(* boatDocked ∈ Banks – the bank where the boat is currently docked *)
(* peopleOnBank ∈ [Banks -> SUBSET People] – mapping each bank to the set
   of people currently on that bank *)

(* ---------------------------------------------------------------------- *)
(*   Safety predicate for a single bank                                   *)
(* ---------------------------------------------------------------------- *)

BankSafe(b) ==
    LET ppl == peopleOnBank[b] IN
    LET mis == Missionaries \cap ppl IN
    LET can == Cannibals    \cap ppl IN
        /\ (mis = {} \/ Cardinality(can) <= Cardinality(mis))

(* ---------------------------------------------------------------------- *)
(*   Overall state predicates                                             *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
    /\ boatDocked \in Banks
    /\ peopleOnBank \in [Banks -> SUBSET People]
    /\ peopleOnBank["East"] \cup peopleOnBank["West"] = People
    /\ peopleOnBank["East"] \cap peopleOnBank["West"] = {}

Solution ==
    /\ peopleOnBank["East"] = {}
    /\ boatDocked = "West"

(* ---------------------------------------------------------------------- *)
(*   Initial state                                                       *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ boatDocked = "East"
    /\ peopleOnBank = [b \in Banks |-> IF b = "East" THEN People ELSE {}]
    /\ TypeOKConsts
    /\ BankSafe("East")
    /\ BankSafe("West")

(* ---------------------------------------------------------------------- *)
(*   Move action (one or two people)                                    *)
(* ---------------------------------------------------------------------- *)

Move ==
    /\ \E load \subseteq peopleOnBank[boatDocked] :
          /\ Cardinality(load) \in {1, 2}
          /\ LET dest == IF boatDocked = "East" THEN "West" ELSE "East" IN
             /\ peopleOnBank' = [b \in Banks |-> 
                    IF b = boatDocked THEN peopleOnBank[b] \ load
                    ELSE IF b = dest   THEN peopleOnBank[b] \cup load
                    ELSE peopleOnBank[b]]
             /\ boatDocked' = dest
    /\ BankSafe(boatDocked')
    /\ BankSafe(dest)

Next ==
    Move

(* ---------------------------------------------------------------------- *)
(*   Specification                                                       *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<boatDocked, peopleOnBank>>

(* ---------------------------------------------------------------------- *)
(*   THEOREM (optional, for TLC)                                         *)
(* ---------------------------------------------------------------------- *)

THEOREM Spec => []TypeOK

=============================================================================