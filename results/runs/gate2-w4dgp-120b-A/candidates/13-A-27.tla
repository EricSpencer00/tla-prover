---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, choosing, ticket, nextTicket

Nat == 0 .. MaxNat

TypeOK ==
    /\ inCS \in [1 .. N -> BOOLEAN]
    /\ choosing \in [1 .. N -> BOOLEAN]
    /\ ticket \in [1 .. N -> Nat]
    /\ nextTicket \in Nat

Init ==
    /\ inCS = [i \in 1 .. N |-> FALSE]
    /\ choosing = [i \in 1 .. N |-> FALSE]
    /\ ticket = [i \in 1 .. N |-> 0]
    /\ nextTicket = 0

Begin(i) ==
    /\ ~inCS[i]
    /\ ~choosing[i]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' =
         IF nextTicket = MaxNat THEN 0 ELSE nextTicket + 1
    /\ UNCHANGED inCS

Enter(i) ==
    /\ choosing[i]
    /\ \A j \in 1 .. N : ~inCS[j]
    /\ \A j \in 1 .. N :
         (j # i /\ choosing[j]) =>
            (ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i))
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, nextTicket>>

Exit(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<choosing, ticket, nextTicket>>

Next ==
    \/ \E i \in 1 .. N : Begin(i)
    \/ \E i \in 1 .. N : Enter(i)
    \/ \E i \in 1 .. N : Exit(i)

Inv ==
    /\ MutualExclusion
    /\ TypeOK

ISpec == Init /\ [][Next]_<<inCS, choosing, ticket, nextTicket>>

====