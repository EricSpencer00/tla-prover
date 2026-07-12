---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANT Ingredients, Offers

VARIABLES smokerState, currentOffer

(* ----------------------------------------------------------------------
   Type definitions (for type checking) ---------------------------------
   ---------------------------------------------------------------------- *)

TypeOK ==
  /\ smokerState \in [Ingredients -> BOOLEAN]
  /\ currentOffer \in (Offers \cup {<<>>})   \* <<>> represents the empty offer

(* ----------------------------------------------------------------------
   Initial state ---------------------------------------------------------
   ---------------------------------------------------------------------- *)

Init ==
  /\ /\ smokerState = [i \in Ingredients |-> FALSE]
     /\ currentOffer \in Offers

(* ----------------------------------------------------------------------
   Actions ---------------------------------------------------------------
   ---------------------------------------------------------------------- *)

(* A smoker whose ingredient combined with the dealer's offer yields the
   full set of Ingredients begins smoking. The offer is then cleared. *)
StartSmoking ==
  \E i \in Ingredients :
      /\ i \in currentOffer
      /\ \A j \in Ingredients : (j \in currentOffer) \/ (j = i)
      /\ smokerState[i] = FALSE
      /\ smokerState' = [smokerState EXCEPT ![i] = TRUE]
      /\ currentOffer' = <<>>

(* After a smoker stops smoking, the dealer places a new offer. *)
StopSmoking ==
  /\ currentOffer = <<>>
  /\ \E i \in Ingredients : smokerState[i] = TRUE
  /\ smokerState' = [smokerState EXCEPT ![i] = FALSE]
  /\ currentOffer' \in Offers

Next ==
  StartSmoking \/ StopSmoking

(* ----------------------------------------------------------------------
   Specification ---------------------------------------------------------
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<smokerState, currentOffer>>

(* ----------------------------------------------------------------------
   Safety invariant: at most one smoker is smoking -----------------------
   ---------------------------------------------------------------------- *)

AtMostOne ==
  CountTrue(smokerState) <= 1

(* ----------------------------------------------------------------------
   Helper function: count number of TRUE values in a Bool mapping -------
   ---------------------------------------------------------------------- *)

CountTrue(m) ==
  Len({i \in Ingredients : m[i] = TRUE})

(* ----------------------------------------------------------------------
   Type invariant (helpful for TLC, not part of the problem statement) --
   ---------------------------------------------------------------------- *)

TypeInvariant ==
  TypeOK

====