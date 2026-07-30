---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES ticket, status, maxTicket

vars == <<ticket, status, maxTicket>>

\* No additional state variables beyond those of the base Bakery model.

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ status \in [1..N -> {"idle", "waiting", "cs"}]
  /\ maxTicket \in 0..MaxNat

\* The inductive invariant: type correctness and all critical-section occupants
\* holding the smallest ticket number equal to the current maximum.
Inv ==
  /\ TypeOK
  /\ \A i \in 1..N : status[i] = "cs" => ticket[i] = maxTicket

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ status = [i \in 1..N |-> "idle"]
  /\ maxTicket = 0

Request(i) ==
  /\ status[i] = "idle"
  /\ maxTicket < MaxNat
  /\ status' = [status EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1

Enter(i) ==
  /\ status[i] = "waiting"
  /\ \A j \in 1..N : (status[j] = "cs") => ticket[i] < ticket[j]
  /\ status' = [status EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, maxTicket>>

Exit(i) ==
  /\ status[i] = "cs"
  /\ status' = [status EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, maxTicket>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

MutualExclusion ==
  \A i \in 1..N, j \in 1..N : (status[i] = "cs" /\ status[j] = "cs") => i = j

ISpec == Init /\ [][Next]_vars

====