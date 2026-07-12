---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, MaxNat, Nat

(*---------------------------------------------------------------------*)
(*  Type definition for the bounded natural numbers                     *)
(*---------------------------------------------------------------------*)
BoundedNat == 0..MaxNat

(*---------------------------------------------------------------------*)
(*  State variables (inherited from the Boulanger specification)        *)
(*  They are declared here for completeness; the actual definitions are *)
(*  assumed to be provided by the imported Boulanger module.            *)
(*---------------------------------------------------------------------*)
VARIABLES Ticket, Choosing, CS

(*---------------------------------------------------------------------*)
(*  Initial state (overrides the natural number range)                  *)
(*---------------------------------------------------------------------*)
Init ==
    /\ Ticket \in [1..N -> 0]
    /\ Choosing = [i \in 1..N |-> FALSE]
    /\ CS = {}

(*---------------------------------------------------------------------*)
(*  Helper definitions                                                     *)
(*---------------------------------------------------------------------*)
MinTicket(i) ==
    \min { Ticket[j] : j \in 1..N }

(*---------------------------------------------------------------------*)
(*  Entry protocol (unchanged from the Boulanger algorithm)              *)
(*---------------------------------------------------------------------*)
Enter(i) ==
    /\ Choosing[i] = FALSE
    /\ Choosing' = [Choosing EXCEPT ![i] = TRUE]
    /\ Ticket' = [Ticket EXCEPT ![i] = MinTicket(i) + 1]
    /\ Choosing' = [Choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED CS

(*---------------------------------------------------------------------*)
(*  Exit protocol (unchanged from the Boulanger algorithm)              *)
(*---------------------------------------------------------------------*)
Exit(i) ==
    /\ Ticket' = [Ticket EXCEPT ![i] = 0]
    /\ CS' = CS \ {i}
    /\ UNCHANGED <<Choosing, Ticket>>

(*---------------------------------------------------------------------*)
(*  Next-state relation                                                     *)
(*---------------------------------------------------------------------*)
Next ==
    \E i \in 1..N :
        /\ i \in CS => Exit(i)
        /\ i \notin CS => Enter(i)

(*---------------------------------------------------------------------*/
(*  Specification                                                          *)
(*---------------------------------------------------------------------*/
Spec == Init /\ [][Next]_<<Ticket, Choosing, CS>>

(*---------------------------------------------------------------------*)
(*  Safety properties (inherited)                                         *)
(*---------------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in CS : i = j

TypeOK ==
    /\ Ticket \in [1..N -> BoundedNat]
    /\ Choosing \in [1..N -> BOOLEAN]
    /\ CS \subseteq 1..N

Inv ==
    Ticket \in [1..N -> BoundedNat] /\ Choosing \in [1..N -> BOOLEAN] /\ CS \subseteq 1..N

====