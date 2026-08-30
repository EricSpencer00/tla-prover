---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

NONE == 0

VARIABLES queue, ticket, status, wants

vars == <<queue, ticket, status, wants>>

TypeOK ==
  /\ queue \in Seq(1 .. N)
  /\ Len(queue) <= N
  /\ ticket \in [1 .. N -> 0 .. MaxNat]
  /\ status \in [1 .. N -> {"idle", "queued", "critical", "slow"}]
  /\ wants \in [1 .. N -> BOOLEAN]

Init ==
  /\ queue = <<>>
  /\ ticket = [p \in 1 .. N |-> 0]
  /\ status = [p \in 1 .. N |-> "idle"]
  /\ wants = [p \in 1 .. N |-> FALSE]

Request(p) ==
  /\ status[p] = "idle"
  /\ status' = [status EXCEPT ![p] = "queued"]
  /\ wants' = [wants EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<queue, ticket>>

Enqueue(p) ==
  /\ status[p] = "queued"
  /\ status' = [status EXCEPT ![p] = "slow"]
  /\ queue' = Append(queue, p)
  /\ UNCHANGED <<ticket, wants>>

Enter(p) ==
  /\ status[p] = "slow"
  /\ Len(queue) > 0
  /\ Head(queue) = p
  /\ \A q \in 1 .. N : status[q] # "critical"
  /\ \A q \in 1 .. N : ticket[q] < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] < MaxNat THEN ticket[p] + 1 ELSE ticket[p]]
  /\ status' = [status EXCEPT ![p] = "critical"]
  /\ queue' = Tail(queue)
  /\ UNCHANGED wants

Exit(p) ==
  /\ status[p] = "critical"
  /\ status' = [status EXCEPT ![p] = "idle"]
  /\ wants' = [wants EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<queue, ticket>>

LeaveQueue ==
  /\ \E i \in 1 .. Len(queue) : status[queue[i]] = "slow"
  /\ \E i \in 1 .. Len(queue) :
       /\ status' = [status EXCEPT ![queue[i]] = "idle"]
       /\ wants' = [wants EXCEPT ![queue[i]] = FALSE]
       /\ queue' = SelectSeq(queue, LAMBDA x : x # queue[i])
  /\ UNCHANGED ticket

Next ==
  \/ \E p \in 1 .. N : Request(p) \/ Enqueue(p) \/ Enter(p) \/ Exit(p)
  \/ LeaveQueue

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1 .. N :
    (status[p] = "critical" /\ status[q] = "critical") => p = q

Inv ==
  /\ \A i \in 1 .. Len(queue) : queue[i] # Head(queue)
  /\ \A i \in 1 .. Len(queue) : status[queue[i]] = "slow"
  /\ \A p \in 1 .. N : status[p] = "queued" => wants[p]

====