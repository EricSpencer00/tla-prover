---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES phase, status, pc, ticket, servedCount, lastServed, act
vars == <<phase, status, pc, ticket, servedCount, lastServed, act>>

TypeOK ==
  /\ phase \in {"idle", "voting"}
  /\ status \in [1..N -> {"idle", "voting", "cs", "aborted"}]
  /\ pc \in [1..N -> 0..2]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ servedCount \in 0..MaxNat
  /\ lastServed \in 0..N
  /\ act \in [1..N -> 0..N]

Init ==
  /\ phase = "idle"
  /\ status = [i \in 1..N |-> "idle"]
  /\ pc = [i \in 1..N |-> 0]
  /\ ticket = [i \in 1..N |-> 0]
  /\ servedCount = 0
  /\ lastServed = 0
  /\ act = [i \in 1..N |-> 0]

Request(i) ==
  /\ phase = "idle"
  /\ status[i] = "idle"
  /\ phase' = "voting"
  /\ status' = [status EXCEPT ![i] = "voting"]
  /\ pc' = [pc EXCEPT ![i] = 1]
  /\ UNCHANGED <<ticket, servedCount, lastServed, act>>

VoteYes(i) ==
  /\ phase = "voting"
  /\ status[i] = "voting"
  /\ pc[i] = 1
  /\ pc' = [pc EXCEPT ![i] = 2]
  /\ UNCHANGED <<phase, status, ticket, servedCount, lastServed, act>>

Enter(i) ==
  /\ phase = "voting"
  /\ status[i] = "voting"
  /\ pc[i] = 2
  /\ status' = [status EXCEPT ![i] = "cs"]
  /\ phase' = "idle"
  /\ UNCHANGED <<pc, ticket, servedCount, lastServed, act>>

Abort(i) ==
  /\ phase = "voting"
  /\ status[i] = "voting"
  /\ pc[i] = 2
  /\ status' = [status EXCEPT ![i] = "aborted"]
  /\ phase' = "idle"
  /\ UNCHANGED <<pc, ticket, servedCount, lastServed, act>>

Exit(i) ==
  /\ status[i] = "cs"
  /\ status' = [status EXCEPT ![i] = "idle"]
  /\ pc' = [pc EXCEPT ![i] = 0]
  /\ servedCount' = IF servedCount < MaxNat THEN servedCount + 1 ELSE servedCount
  /\ lastServed' = i
  /\ UNCHANGED <<phase, ticket, act>>

Grant(i) ==
  /\ act[i] = 0
  /\ \A j \in 1..N : act[j] = 0
  /\ \E k \in 1..N : act' = [act EXCEPT ![i] = k]
  /\ UNCHANGED <<phase, status, pc, ticket, servedCount, lastServed>>

Release(i) ==
  /\ act[i] # 0
  /\ act' = [act EXCEPT ![i] = 0]
  /\ UNCHANGED <<phase, status, pc, ticket, servedCount, lastServed>>

Reconfig ==
  /\ \A j \in 1..N : status[j] = "idle"
  /\ \A j \in 1..N : ticket[j] = 0
  /\ \E i \in 1..N :
       /\ ticket' = [ticket EXCEPT ![i] = IF ticket[i] < MaxNat THEN ticket[i] + 1 ELSE ticket[i]]
       /\ act' = [act EXCEPT ![i] = 0]
  /\ UNCHANGED <<phase, status, pc, servedCount, lastServed>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : VoteYes(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Abort(i)
  \/ \E i \in 1..N : Exit(i)
  \/ \E i \in 1..N : Grant(i)
  \/ \E i \in 1..N : Release(i)
  \/ Reconfig

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i \in 1..N : status[i] = "cs" => (\A k \in 1..N : k # i => status[k] # "cs")

Inv ==
  /\ \A i \in 1..N : status[i] = "cs" => act[i] = 1
  /\ \A i \in 1..N : status[i] = "cs" => (servedCount < MaxNat /\ lastServed = i)
  /\ \A i \in 1..N : status[i] # "cs" => act[i] = 0
  /\ \A i \in 1..N : status[i] # "idle" => status[i] = status[act[i]]
  /\ \A i \in 1..N : status[i] = "cs" => (servedCount = 0 \/ lastServed = i)
  /\ \A i \in 1..N : status[i] = "idle" => act[i] = 0

BoundState == \A i \in 1..N : ticket[i] < MaxNat
====