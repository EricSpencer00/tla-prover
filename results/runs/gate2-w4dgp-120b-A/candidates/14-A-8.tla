---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES pc, turn, flag, want, ticket, mem

vars == <<pc, turn, flag, want, ticket, mem>>

Range(s) == {s[i] : i \in DOMAIN s}

Bump(n) == IF n = MaxNat THEN 0 ELSE n

TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "crit"}]
  /\ turn \in 0..N
  /\ flag \in [1..N -> {"idle", "trying"}]
  /\ want \in [1..N -> 0..N]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ mem \in 0..N

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ turn = 0
  /\ flag = [i \in 1..N |-> "idle"]
  /\ want = [i \in 1..N |-> 0]
  /\ ticket = [i \in 1..N |-> 0]
  /\ mem = 0

Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "trying"]
  /\ flag' = [flag EXCEPT ![i] = "trying"]
  /\ want' = [want EXCEPT ![i] = turn]
  /\ ticket' = [ticket EXCEPT ![i] = Bump(ticket[i])]
  /\ UNCHANGED <<turn, mem>>

Enter(i) ==
  /\ pc[i] = "trying"
  /\ turn = want[i]
  /\ \A j \in 1..N : j # i => (flag[j] = "idle" \/ want[j] # want[i] \/ ticket[j] > ticket[i])
  /\ turn' = i
  /\ pc' = [pc EXCEPT ![i] = "crit"]
  /\ UNCHANGED <<flag, want, ticket, mem>>

Exit(i) ==
  /\ pc[i] = "crit"
  /\ turn' = 0
  /\ flag' = [flag EXCEPT ![i] = "idle"]
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<want, ticket, mem>>

Read(i) ==
  /\ pc[i] = "crit"
  /\ mem < i
  /\ mem' = i
  /\ UNCHANGED <<pc, turn, flag, want, ticket>>

Spec == Init /\ [][Next]_vars
  /\ \A i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i) \/ Read(i)

MutualExclusion == \A i \in 1..N : pc[i] = "crit" => turn = i

Inv ==
  /\ (Range(pc) \subseteq {"idle", "trying", "crit"})
  /\ turn \in 0..N
  /\ (Range(flag) \subseteq {"idle", "trying"})
  /\ (Range(want) \subseteq 0..N)
  /\ (Range(ticket) \subseteq 0..MaxNat)
  /\ mem \in 0..N

NatOverride == Nat

====