---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES used, ticket, pstate, maxTicket
vars == <<used, ticket, pstate, maxTicket>>

ASSUME N \in Nat \ {0}

\* Under the inductive spec, any type-correct reachable state may be the start
\* (Init only for initial-state checking, InitAny for the inductive base).
Init == /\ used = [p \in 1..N |-> FALSE]
        /\ ticket = [p \in 1..N |-> 0]
        /\ pstate = [p \in 1..N |-> "idle"]
        /\ maxTicket = 0

InitAny == /\ \E u \in [1..N -> BOOLEAN], tk \in [1..N -> 0..MaxNat],
               ps \in [1..N -> {"idle", "waiting", "cs"}], m \in 0..MaxNat :
                 /\ used = u
                 /\ ticket = tk
                 /\ pstate = ps
                 /\ maxTicket = m
                 /\ TypeOK

TypeOK == /\ used \in [1..N -> BOOLEAN]
          /\ ticket \in [1..N -> 0..MaxNat]
          /\ pstate \in [1..N -> {"idle", "waiting", "cs"}]
          /\ maxTicket \in 0..MaxNat

\* A process picks a fresh ticket bounded by the global MaxNat.
Request(p) == /\ pstate[p] = "idle"
               /\ ~used[p]
               /\ LET nt == IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket IN
                    /\ ticket' = [ticket EXCEPT ![p] = nt]
                    /\ maxTicket' = nt
               /\ pstate' = [pstate EXCEPT ![p] = "waiting"]
               /\ UNCHANGED <<used>>

\* A waiting process may enter the critical section only when it is not behind
\* another waiting process that holds a strictly smaller ticket.
Enter(p) == /\ pstate[p] = "waiting"
             /\ \A q \in 1..N : (pstate[q] = "waiting" /\ ticket[q] < ticket[p]) => FALSE
             /\ pstate' = [pstate EXCEPT ![p] = "cs"]
             /\ UNCHANGED <<used, ticket, maxTicket>>

Exit(p) == /\ pstate[p] = "cs"
           /\ pstate' = [pstate EXCEPT ![p] = "idle"]
           /\ used' = [used EXCEPT ![p] = TRUE]
           /\ UNCHANGED <<ticket, maxTicket>>

Next == \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

\* The inductive spec: any type-correct reachable state may be the start.
Spec == Init \/ InitAny \/ Next

MutualExclusion == \A a, b \in 1..N : (pstate[a] = "cs" /\ pstate[b] = "cs") => a = b

\* The bakery invariant: any process in the critical section is waiting on the
\* smallest ticket among everyone still waiting.
Inv == \A p \in 1..N : pstate[p] = "cs" => \A q \in 1..N :
         (pstate[q] = "waiting") => ticket[p] <= ticket[q]

====