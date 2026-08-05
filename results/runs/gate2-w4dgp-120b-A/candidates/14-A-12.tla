---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES pc, ticket, highest, served
vars == <<pc, ticket, highest, served>>

Processes == 1..N

NatOverride == 0..MaxNat

Spec ==
    /\ \E pc0 \in [Processes -> {"idle","waiting","critical"}],
         ticket0 \in [Processes -> NatOverride],
         highest0 \in NatOverride,
         served0 \in [Processes -> NatOverride] :
         /\ pc = pc0
         /\ ticket = ticket0
         /\ highest = highest0
         /\ served = served0
    /\ \A p \in Processes :
         \/ (pc[p] = "waiting" /\ highest < MaxNat /\ ticket' = [ticket EXCEPT ![p] = highest + 1] /\ highest' = highest + 1 /\ UNCHANGED <<pc, served>>)
         \/ (pc[p] = "waiting" /\ highest = MaxNat /\ UNCHANGED vars)
    /\ \A p \in Processes : pc[p] # "waiting" => UNCHANGED vars

Init ==
    /\ pc = [p \in Processes |-> "idle"]
    /\ ticket = [p \in Processes |-> 0]
    /\ highest = 0
    /\ served = [p \in Processes |-> 0]

MutualExclusion ==
    \A p \in Processes :
        (pc[p] = "critical") =>
            (\A q \in Processes :
                (pc[q] = "critical") => (q = p))

TypeOK ==
    /\ pc \in [Processes -> {"idle","waiting","critical"}]
    /\ ticket \in [Processes -> NatOverride]
    /\ highest \in NatOverride

Inv ==
    /\ \A p \in Processes :
         (pc[p] = "critical") =>
            (\A q \in Processes : (q # p /\ pc[q] = "critical") => (ticket[p] < ticket[q]))
    /\ \A p \in Processes : (pc[p] = "critical") => (served[p] = 0)

StateConstraint == \A p \in Processes : ticket[p] < MaxNat

====