---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

ASSUME N \in Nat \ {0}

VARIABLES door, ticket, inCS, nextTicket, free

vars == <<door, ticket, inCS, nextTicket, free>>

Bump(v) == IF v = MaxNat THEN 0 ELSE v + 1

TypeOK ==
  /\ door \in {"open", "closed"}
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ nextTicket \in 1..(MaxNat + 1)
  /\ free \in BOOLEAN

Init ==
  /\ door = "open"
  /\ ticket = [i \in 1..N |-> 0]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ nextTicket = 1
  /\ free = TRUE

Enter(i) ==
  /\ door = "open"
  /\ free
  /\ ticket[i] = 0
  /\ free' = FALSE
  /\ door' = "closed"
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = Bump(nextTicket)
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED free

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ free' = TRUE
  /\ door' = "open"
  /\ UNCHANGED <<nextTicket, free>>

AdminOverride(i) ==
  /\ free
  /\ free' = FALSE
  /\ door' = "closed"
  /\ ticket' = [j \in 1..N |-> IF j = i THEN nextTicket ELSE ticket[j]]
  /\ nextTicket' = Bump(nextTicket)
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED free

AdminClear ==
  /\ ~free
  /\ free' = TRUE
  /\ door' = "open"
  /\ ticket' = [i \in 1..N |-> 0]
  /\ inCS' = [i \in 1..N |-> FALSE]
  /\ UNCHANGED nextTicket

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)
  \/ \E i \in 1..N : AdminOverride(i)
  \/ AdminClear

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : inCS[i] => (door = "closed" /\ ticket[i] # 0)

Inv ==
  \A i \in 1..N :
    (inCS[i] <=> (door = "closed" /\ ticket[i] # 0))

TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====