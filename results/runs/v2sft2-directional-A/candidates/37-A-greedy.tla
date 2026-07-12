---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Ingredients \cup {<<>>}

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

StartSmoking ==
    /\ offer # <<>>
    /\ \E i \in Ingredients :
          /\ offer = Ingredients \ {i}
          /\ smoking[i] = FALSE
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ offer' = <<>>
    /\ UNCHANGED <<>>

StopSmoking ==
    /\ offer = <<>>
    /\ \E i \in Ingredients : smoking[i] = TRUE
    /\ \E o \in Offers : offer' = o
    /\ smoking' = [i \in Ingredients |-> FALSE]
    /\ UNCHANGED <<>>

Next ==
    StartSmoking \/ StopSmoking

Spec ==
    Init /\ [][Next]_<<smoking, offer>>

(* ----------------------------------------------------------------------
   Safety invariant: at most one smoker is smoking
   ---------------------------------------------------------------------- *)
AtMostOne ==
    Cardinality({i \in Ingredients : smoking[i]}) <= 1

====