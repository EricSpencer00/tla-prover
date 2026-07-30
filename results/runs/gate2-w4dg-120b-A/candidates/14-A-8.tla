---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES cs, waiting, ticket, nextTicket, served
vars == <<cs, waiting, ticket, nextTicket, served>>

TypeOK ==
  /\ cs \in [1..N -> BOOLEAN]
  /\ waiting \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ served \in 0..MaxNat

Init ==
  /\ cs = [i \in 1..N |-> FALSE]
  /\ waiting = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ served = 0

Enter(i) ==
  /\ ~cs[i]
  /\ waiting[i] = FALSE
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ waiting' = [waiting EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<cs, served>>

Admit(i) ==
  /\ waiting[i]
  /\ \A j \in 1..N : ~cs[j] => ticket[i] < ticket[j]
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ waiting' = [waiting EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket, served>>

Exit(i) ==
  /\ cs[i]
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ served' = IF served < MaxNat THEN served + 1 ELSE served
  /\ UNCHANGED <<waiting, ticket, nextTicket>>

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Admit(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : cs[i] => (\A j \in 1..N : i # j => ~cs[j])

Inv ==
  \A i \in 1..N :
    /\ cs[i] => \A j \in 1..N : (cs[j] /\ i # j => ticket[i] < ticket[j])
    /\ waiting[i] => \A j \in 1..N : cs[j] => ticket[i] <= ticket[j]

TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====