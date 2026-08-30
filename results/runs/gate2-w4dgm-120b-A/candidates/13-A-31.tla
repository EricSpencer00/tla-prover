---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES phase, want, ticket, inbox

vars == <<phase, want, ticket, inbox>>

TypeOK ==
  /\ phase \in [1..N -> {"idle", "trying", "inCS"}]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ inbox \in SUBSET [proc: 1..N, val: 0..MaxNat]

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ want = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ inbox = {}

Enter(i) ==
  /\ phase[i] = "idle"
  /\ \A j \in 1..N : phase[j] # "inCS"
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ phase' = [phase EXCEPT ![i] = "trying"]
  /\ UNCHANGED <<ticket, inbox>>

Claim(i) ==
  /\ phase[i] = "trying"
  /\ want[i]
  /\ \A j \in 1..N : phase[j] # "inCS"
  /\ \A j \in 1..N : phase[j] # "trying" => ticket[j] < ticket[i]
  /\ phase' = [phase EXCEPT ![i] = "inCS"]
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, inbox>>

Leave(i) ==
  /\ phase[i] = "inCS"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<want, ticket, inbox>>

Reconfigure(i) ==
  /\ phase[i] = "idle"
  /\ \E t \in 0..MaxNat : ticket' = [ticket EXCEPT ![i] = t]
  /\ UNCHANGED <<phase, want, inbox>>

Send(i, v) ==
  /\ inbox' = inbox \cup {[proc |-> i, val |-> v]}
  /\ UNCHANGED <<phase, want, ticket>>

Apply(e) ==
  /\ e \in inbox
  /\ ticket' = [ticket EXCEPT ![e.proc] = e.val]
  /\ inbox' = inbox \ {e}
  /\ UNCHANGED <<phase, want>>

Next ==
  \/ \E i \in 1..N : Enter(i) \/ Claim(i) \/ Leave(i) \/ Reconfigure(i)
  \/ \E i \in 1..N, v \in 0..MaxNat : Send(i, v)
  \/ \E e \in inbox : Apply(e)

InductiveInit ==
  /\ \E i \in 1..N : phase[i] \in {"idle", "trying", "inCS"}
  /\ \E i \in 1..N : want[i] \in BOOLEAN
  /\ \E i \in 1..N : ticket[i] \in 0..MaxNat
  /\ inbox \in SUBSET [proc: 1..N, val: 0..MaxNat]

MutualExclusion ==
  \A i, j \in 1..N :
    (phase[i] = "inCS" /\ phase[j] = "inCS") => i = j

Inv == MutualExclusion

ISpec == Init /\ [][Next]_vars

====