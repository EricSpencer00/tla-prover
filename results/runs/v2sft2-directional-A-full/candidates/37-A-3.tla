---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

(* Type definitions *)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Union(Offers)

(* Initial state *)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers: offer = o

(* Smokers start smoking when the offer, together with their own ingredient,
   yields the full set of Ingredients. *)
StartSmoking ==
    LET s == CHOOSE i \in Ingredients :
              /\ offer \cup {i} = Ingredients
              /\ ~smoking[i]
    IN /\ smoking' = [smoking EXCEPT ![s] = TRUE]
       /\ offer'  = {}

(* Smokers stop smoking when the offer is empty. Only the currently smoking
   smoker stops, and a new offer is chosen nondeterministically. *)
StopSmoking ==
    /\ offer = {}
    /\ \E s \in Ingredients :
           /\ smoking[s] = TRUE
           /\ \A i \in Ingredients \ {s} : smoking[i] = FALSE
    /\ /\ smoking' = [i \in Ingredients |-> FALSE]
       /\ offer'  \in Offers

(* Next-state relation *)
Next ==
    \/ StartSmoking
    \/ StopSmoking

(* Specification *)
Spec == Init /\ [][Next]_<<smoking, offer>>

(* At most one smoker is smoking. *)
AtMostOne ==
    Len({i \in Ingredients : smoking[i]}) <= 1

====