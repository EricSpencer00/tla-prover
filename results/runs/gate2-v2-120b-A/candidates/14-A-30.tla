---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* State variables (same as in the original Boulanger spec)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket, nextTicket

\* ----------------------------------------------------------------------
\* Helper definitions (mirroring the original Boulanger spec)
\* ----------------------------------------------------------------------
Idle      == "idle"
Request   == "request"
CS        == "cs"
Done      == "done"
Home      == "home"
Next      == "next"

Nexts    == Seq("next")
Alist    == Seq("idle", "request", "cs", "done", "home", "next")

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> Idle]
    /\ ticket = [i \in Proc |-> 0]
    /\ nextTicket = 0

\* ----------------------------------------------------------------------
\* Actions (identical to those in the original Boulanger specification)
\* ----------------------------------------------------------------------
Request(i) ==
    /\ pc[i] = Idle
    /\ pc' = [pc EXCEPT ![i] = Request]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = nextTicket + 1

Take(i) ==
    /\ pc[i] = Request
    /\ \A j \in Proc :
         (pc[j] \in {Idle, Request, CS}) => 
            ( ticket[i] < ticket[j] \/
              (ticket[i] = ticket[j] /\ i < j) )
    /\ pc' = [pc EXCEPT ![i] = CS]
    /\ UNCHANGED <<ticket, nextTicket>>

Release(i) ==
    /\ pc[i] = CS
    /\ pc' = [pc EXCEPT ![i] = Done]
    /\ UNCHANGED <<ticket, nextTicket>>

Done(i) ==
    /\ pc[i] = Done
    /\ pc' = [pc EXCEPT ![i] = Idle]
    /\ UNCHANGED <<ticket, nextTicket>>

Next(i) ==
    /\ pc[i] = Home
    /\ pc' = [pc EXCEPT ![i] = Idle]
    /\ UNCHANGED <<ticket, nextTicket>>

\* ----------------------------------------------------------------------
\* Stuttering step (allows the model to idle)
\* ----------------------------------------------------------------------
Stutter ==
    UNCHANGED <<pc, ticket, nextTicket>>

\* ----------------------------------------------------------------------
\* Next-state relation (disjunction of all actions)
\* ----------------------------------------------------------------------
Next ==
    \E i \in Proc :
        \/ Request(i)
        \/ Take(i)
        \/ Release(i)
        \/ Done(i)
        \/ Next(i)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~(pc[i] = CS /\ pc[j] = CS)

TypeOK ==
    /\ pc \in [Proc -> Alist]
    /\ ticket \in [Proc -> Nat]
    /\ nextTicket \in Nat
    /\ nextTicket <= MaxNat

RangeOK ==
    /\ \A i \in Proc : ticket[i] < MaxNat

Inv == MutualExclusion /\ TypeOK /\ RangeOK

\* ----------------------------------------------------------------------
\* State constraint to keep ticket numbers strictly below MaxNat
\* ----------------------------------------------------------------------
StateConstraint == RangeOK

====