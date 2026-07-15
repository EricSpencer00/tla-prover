---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

(* The set of all ingredients, e.g., {"matches", "paper", "tobacco"} *)

VARIABLES smoker, offer

(* smoker maps each ingredient to a Boolean indicating whether the smoker
   who owns that ingredient is currently smoking. *)
(* offer is either a subset of Ingredients (the current table offer) or
   the empty set, which signals that a smoker is currently smoking. *)

(*------------------------------*)
(*   Type correctness (helper) *)
(*------------------------------*)
SmokerOK == smoker \in [Ingredients -> BOOLEAN]
OfferOK  == offer \in (Offers \cup {{} })

TypeOK == SmokerOK /\ OfferOK

(*------------------------------*)
(*       Initial state          *)
(*------------------------------*)
Init ==
    /\ smoker = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers            \* a nondeterministic valid offer

(*------------------------------*)
(*       Actions                *)
(*------------------------------*)

(* A smoker whose ingredient completes the set starts smoking.
   The offer must be non‑empty, exactly one smoker can start, and the
   offer is cleared. *)
StartSmoking ==
    \E i \in Ingredients :
        /\ i \notin offer                 \* i is the missing ingredient
        /\ /\ \A j \in Ingredients : j # i => j \in offer
        /\ smoker[i] = FALSE
        /\ smoker' = [smoker EXCEPT ![i] = TRUE]
        /\ offer' = {}

(* The currently‑smoking smoker stops and the dealer places a new offer. *)
StopSmoking ==
    \E i \in Ingredients :
        /\ smoker[i] = TRUE
        /\ offer = {}
        /\ smoker' = [smoker EXCEPT ![i] = FALSE]
        /\ offer' \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

(*------------------------------*)
(*       Specification          *)
(*------------------------------*)
Spec == Init /\ [][Next]_<<smoker, offer>>

(*------------------------------*)
(*       Invariant               *)
(*------------------------------*)
AtMostOne ==
    Cardinality({ i \in Ingredients : smoker[i] }) <= 1

=============================================================================