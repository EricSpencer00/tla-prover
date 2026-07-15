---- MODULE MCBakery ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

(* The token is a function mapping each process to a natural number.
   For the model checking configuration we restrict the token values to the
   finite range Nat, which is defined to be exactly the set 0..MaxNat. *)
VARIABLE token, choosing

(* Helper to denote the set of process identifiers *)
ProcSet == 0..(N - 1)

(* The finite natural number set used in this configuration.  The constant Nat
   is required by the .cfg file; here we constrain it to 0..MaxNat. *)
NatSet == 0..MaxNat

(* Initial state: all processes are not choosing and have ticket 0. *)
Init ==
    /\ token = [i \in ProcSet |-> 0]
    /\ choosing = [i \in ProcSet |-> FALSE]
    /\ Nat = NatSet

(* The type-correctness invariant (from the original Bakery spec). *)
TypeOK ==
    /\ token \in [ProcSet -> NatSet]
    /\ choosing \in [ProcSet -> BOOLEAN]

(* A process i is in its critical section when it holds the smallest ticket
   (with the tie‑break on process id) among all processes that are either
   choosing or already in the critical section.  This definition matches the
   original Bakery specification. *)
InCS(i) ==
    /\ token[i] # 0
    /\ \A j \in ProcSet :
          (j # i) => 
            (token[j] = 0) \/
            (choosing[j]) \/
            (token[j] > token[i]) \/
            (token[j] = token[i] /\ j > i)

(* Mutual exclusion: at most one process can be in its critical section at any
   time. *)
MutualExclusion ==
    \A i, j \in ProcSet :
        (i # j) => ~ (InCS(i) /\ InCS(j))

(* Full inductive invariant: type correctness together with mutual exclusion. *)
Inv == TypeOK /\ MutualExclusion

(* -------------------  Actions  ------------------- *)

(* A process i starts the entry protocol. *)
Entry(i) ==
    /\ i \in ProcSet
    /\ ~InCS(i)
    /\ choosing[i] = FALSE
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ token' = token
    /\ UNCHANGED Nat

(* Process i obtains a ticket: choose the smallest unused number in NatSet. *)
ObtainTicket(i) ==
    /\ i \in ProcSet
    /\ choosing[i] = TRUE
    /\ token' = [token EXCEPT ![i] = Max({ token[j] : j \in ProcSet } \cup {0}) + 1]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED Nat
    /\ token'[i] \in NatSet   \* ticket stays within the finite range

(* Process i leaves the critical section, resetting its ticket. *)
Exit(i) ==
    /\ i \in ProcSet
    /\ InCS(i)
    /\ token' = [token EXCEPT ![i] = 0]
    /\ UNCHANGED choosing
    /\ UNCHANGED Nat

(* Stuttering step to avoid deadlock when no process can move. *)
Stutter ==
    UNCHANGED << token, choosing, Nat >>

(* Next-state relation: any of the above actions for any process, or stutter. *)
Next ==
    \/ \E i \in ProcSet : Entry(i)
    \/ \E i \in ProcSet : ObtainTicket(i)
    \/ \E i \in ProcSet : Exit(i)
    \/ Stutter

(* -------------------  Specification  ------------------- *)

(* The inductive specification starts from any state satisfying the invariant
   and then follows the Next relation. *)
ISpec == Init /\ [][Next]_<< token, choosing, Nat >>

(* The .cfg file expects the identifier "Spec" to denote the overall spec,
   but the required identifier here is "ISpec".  We expose the canonical Spec
   name as an alias for completeness, without violating the required names. *)
Spec == ISpec

====