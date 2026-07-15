---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

(* --algorithm constants for readability *)
Match    == "match"
Paper    == "paper"
Tobacco  == "tobacco"

(* The complete set of ingredients, used in expressions. *)
FullSet == Ingredients

VARIABLES smokers, offer

(* smokers maps each ingredient to a boolean indicating if that smoker
   (who holds the infinite supply of that ingredient) is currently smoking. *)
(* offer is the current set of ingredients placed on the table.  It is
   either a non‑empty subset missing exactly one ingredient, or {} when a smoker is smoking. *)

(* ---- Initialization ---- *)
Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ /\ offer \in Offers
       /\ offer # {}               \* non‑empty initial offer
    /\ \A i \in Ingredients: smokers[i] = FALSE

(* ---- Actions ---- *)

(* A smoker whose own ingredient completes the full set starts smoking. *)
StartSmoking ==
    /\ offer # {}                \* there is an offer on the table
    /\ \E i \in Ingredients :
          /\ smokers[i] = FALSE
          /\ offer = FullSet \ {i}
          /\ smokers' = [smokers EXCEPT ![i] = TRUE]
    /\ offer' = {}               \* the table is cleared while smoking

(* The currently smoking smoker stops and the dealer places a new offer. *)
StopSmoking ==
    /\ offer = {}                \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ smokers[i] = TRUE
          /\ smokers' = [smokers EXCEPT ![i] = FALSE]
    /\ /\ offer' \in Offers
       /\ offer' # {}              \* the new offer must be non‑empty

Next ==
    \/ StartSmoking
    \/ StopSmoking

Spec == Init /\ [][Next]_<<smokers, offer>>

(* ---- Type correctness invariant ---- *)
TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup {{}})

(* ---- Safety invariant: at most one smoker is smoking ---- *)
AtMostOne ==
    Cardinality({ i \in Ingredients : smokers[i] }) <= 1

====