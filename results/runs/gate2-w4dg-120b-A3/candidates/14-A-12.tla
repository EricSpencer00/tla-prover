---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, pc, ticket, nextTicket

vars == << cs, pc, ticket, nextTicket >>

TypeOK ==
  /\ cs \in [1..N -> {"idle", "trying", "cs"}]
  /\ pc \in [1..N -> 0..MaxNat]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ cs = [i \in 1..N |-> "idle"]
  /\ pc = [i \in 1..N |-> 0]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

Try(i) ==
  /\ cs[i] = "idle"
  /\ cs' = [cs EXCEPT ![i] = "trying"]
  /\ pc' = [pc EXCEPT ![i] = (pc[i] + 1) % (MaxNat + 1)]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)

Enter(i) ==
  /\ cs[i] = "trying"
  /\ \A j \in 1..N : (cs[j] = "cs") => (ticket[j] > ticket[i])
  /\ cs' = [cs EXCEPT ![i] = "cs"]
  /\ UNCHANGED << pc, ticket, nextTicket >>

Exit(i) ==
  /\ cs[i] = "cs"
  /\ cs' = [cs EXCEPT ![i] = "idle"]
  /\ UNCHANGED << pc, ticket, nextTicket >>

Next ==
  \/ \E i \in 1..N : Try(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec ==
  /\ Init
  /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (cs[i] = "cs" /\ cs[j] = "cs") => i = j

Inv == TypeOK /\ MutualExclusion

StateBound == \A i \in 1..N : ticket[i] < MaxNat

====