---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The underlying Boulanger spec from which this config module inherits.
\* N is the number of concurrent processes; MaxNat is the highest
\* ticket number explored under model checking; Nat is the finite
\* range of natural numbers substituted for the infinite NAT.
VARIABLES active, ticket, served, phase

vars == <<active, ticket, served, phase>>

States == {"idle", "trying", "critical"}

TypeOK ==
  /\ active \in [0..(N-1) -> BOOLEAN]
  /\ ticket \in [0..(N-1) -> 0..(MaxNat - 1)]
  /\ served \in 0..N
  /\ phase \in [0..(N-1) -> States]

Init ==
  /\ active = [p \in 0..(N-1) |-> FALSE]
  /\ ticket = [p \in 0..(N-1) |-> 0]
  /\ served = 0
  /\ phase = [p \in 0..(N-1) |-> "idle"]

\* A process that wants the critical section marks itself and picks a
\* fresh ticket number; the ticket is only valid while below MaxNat.
Request(p) ==
  /\ phase[p] = "idle"
  /\ ~active[p]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ phase' = [phase EXCEPT ![p] = "trying"]
  /\ UNCHANGED <<active, served>>

Take(p) ==
  /\ phase[p] = "trying"
  /\ \A q \in 0..(N-1) : ~active[q]
  /\ ticket[p] < MaxNat
  /\ active' = [active EXCEPT ![p] = TRUE]
  /\ phase' = [phase EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<ticket, served>>

Release(p) ==
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ served' = (served + 1) % N
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ UNCHANGED ticket

Reissue(p) ==
  /\ phase[p] = "trying"
  /\ active[p] = FALSE
  /\ served > 0
  /\ ticket[p] < MaxNat - 1
  /\ ticket' = [ticket EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<active, served, phase>>

Next ==
  \/ \E p \in 0..(N-1) : Request(p) \/ Take(p) \/ Release(p) \/ Reissue(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 0..(N-1) : Request(p))
  /\ WF_vars(\E p \in 0..(N-1) : Take(p))
  /\ WF_vars(\E p \in 0..(N-1) : Release(p))

MutualExclusion ==
  \A p, q \in 0..(N-1) : (active[p] /\ active[q]) => p = q

Inv ==
  /\ active \in [0..(N-1) -> BOOLEAN]
  /\ ticket \in [0..(N-1) -> 0..(MaxNat - 1)]
  /\ served \in 0..N
  /\ phase \in [0..(N-1) -> States]

StateConstraint ==
  \A p \in 0..(N-1) : ticket[p] < MaxNat

====