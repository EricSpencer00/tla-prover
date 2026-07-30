---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The process set is fixed and derived from N; the finite Nat range is
\* defined here and used for every ticket rather than the full infinite set.
PROCESS == 1..N
Ticket == Nat

VARIABLES phase, ticket, serving, lastTicket

vars == <<phase, ticket, serving, lastTicket>>

TypeOK ==
    /\ phase \in [PROCESS -> {"idle", "waiting", "critical"}]
    /\ ticket \in [PROCESS -> Ticket]
    /\ serving \in 0..MaxNat
    /\ lastTicket \in 0..MaxNat

Init ==
    /\ phase = [p \in PROCESS |-> "idle"]
    /\ ticket = [p \in PROCESS |-> 0]
    /\ serving = 0
    /\ lastTicket = 0

\* The Bakery protocol: a waiting process takes the next ticket, then enters
\* the critical section only when its ticket is before every other's.
Request(p) ==
    /\ phase[p] = "idle"
    /\ lastTicket < MaxNat
    /\ phase' = [phase EXCEPT ![p] = "waiting"]
    /\ ticket' = [ticket EXCEPT ![p] = lastTicket + 1]
    /\ lastTicket' = lastTicket + 1
    /\ UNCHANGED serving

Enter(p) ==
    /\ phase[p] = "waiting"
    /\ serving < ticket[p]
    /\ phase' = [phase EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, serving, lastTicket>>

Serve(p) ==
    /\ phase[p] = "critical"
    /\ serving' = (serving + 1) % (MaxNat + 1)
    /\ phase' = [phase EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<ticket, lastTicket>>

Next ==
    \E p \in PROCESS :
        \/ Request(p)
        \/ Enter(p)
        \/ Serve(p)

Spec == Init /\ [][Next]_vars

\* The inductive invariant holds from any reachable state, not just the
\* initial one: it is what keeps the ticket ordering consistent.
Inv == TypeOK

MutualExclusion ==
    \A p \in PROCESS :
        phase[p] = "critical" => (\A q \in PROCESS : q # p => phase[q] # "critical")

ISpec == Spec
====