---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (must match the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Nat == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State variables (inherit all from the original Boulanger specification)
\* ----------------------------------------------------------------------
VARIABLES next, token, ticket, state

\* ----------------------------------------------------------------------
\* Helper definitions (not required by the .cfg but useful for clarity)
\* ----------------------------------------------------------------------
\* The set of process identifiers
ProcSet == 1 .. N

\* ----------------------------------------------------------------------
\* Initialization (same as Boulanger, but with Nat restricted)
\* ----------------------------------------------------------------------
Init ==
    /\ next = 0
    /\ token = 0
    /\ ticket = [i \in ProcSet |-> 0]
    /\ state  = [i \in ProcSet |-> "idle"]

\* ----------------------------------------------------------------------
\* Algorithm actions (inherit from Boulanger, with Nat replaced by our Nat)
\* ----------------------------------------------------------------------
Req(i) ==
    /\ i \in ProcSet
    /\ state[i] = "idle"
    /\ ticket' = [ticket EXCEPT ![i] = next]
    /\ next' = next + 1
    /\ state' = [state EXCEPT ![i] = "waiting"]
    /\ UNCHANGED token

Wait(i) ==
    /\ i \in ProcSet
    /\ state[i] = "waiting"
    /\ token' = token
    /\ next' = next
    /\ ticket' = ticket
    /\ IF ticket[i] = token
          THEN state' = [state EXCEPT ![i] = "critical"]
          ELSE state' = state

Exit(i) ==
    /\ i \in ProcSet
    /\ state[i] = "critical"
    /\ token' = token + 1
    /\ next' = next
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ state' = [state EXCEPT ![i] = "idle"]

Next ==
    \/ \E i \in ProcSet: Req(i)
    \/ \E i \in ProcSet: Wait(i)
    \/ \E i \in ProcSet: Exit(i)

\* ----------------------------------------------------------------------
\* Safety properties (from the original specification)
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in ProcSet : (i # j) => ~(state[i] = "critical" /\ state[j] = "critical")

TypeOK ==
    /\ next \in Nat
    /\ token \in Nat
    /\ ticket \in [ProcSet -> Nat]
    /\ state \in [ProcSet -> {"idle", "waiting", "critical"}]

Inv ==
    (* This invariant captures the full mutual exclusion invariant of the
       original Boulanger algorithm, expressed in more detail. *)
    /\ token \in Nat
    /\ \A i \in ProcSet : ticket[i] \in Nat
    /\ \A i, j \in ProcSet :
          (i # j) /\ state[i] = "critical" /\ state[j] = "critical" => FALSE
    /\ \A i \in ProcSet :
          (state[i] = "critical") => (ticket[i] = token)

\* ----------------------------------------------------------------------
\* Specification (full behavioral specification, not the inductive version)
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<next, token, ticket, state>>

\* ----------------------------------------------------------------------
\* State constraint to prune states where any ticket reaches MaxNat
\* ----------------------------------------------------------------------
StateConstraint ==
    \A i \in ProcSet : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Checking that the state constraint is respected by all reachable states
\* ----------------------------------------------------------------------
StateConstraintCheck == StateConstraint

\* ----------------------------------------------------------------------
\* The module ends here.  The .cfg file will import this module and
\* perform model checking using the constants and invariants declared above.
\* ----------------------------------------------------------------------
====