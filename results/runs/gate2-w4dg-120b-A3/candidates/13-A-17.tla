---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES pc, choosing, number
vars == <<pc, choosing, number>>

Tickets == 0..MaxNat

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ number = [i \in 1..N |-> 0]

Choose(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED number

TakeNumber(i) ==
  /\ pc[i] = "waiting"
  /\ choosing[i]
  /\ number' = [number EXCEPT ![i] =
                 IF \E j \in 1..N : number[j] > number[i] /\ number[j] < MaxNat
                    THEN number[i] + 1
                    ELSE number[i]]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED pc

Enter(i) ==
  /\ pc[i] = "waiting"
  /\ ~choosing[i]
  /\ \A j \in 1..N : pc[j] # "critical" \/ (number[i] < number[j] \/ (number[i] = number[j] /\ i < j))
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<choosing, number>>

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ number' = [number EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Next ==
  \/ \E i \in 1..N : Choose(i) \/ TakeNumber(i) \/ Enter(i) \/ Exit(i)

Next == Next

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : pc[i] = "critical" => \A j \in 1..N : j # i => pc[j] # "critical"

TypeOK ==
  /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ number \in [1..N -> Tickets]

Inv ==
  /\ MutualExclusion
  /\ TypeOK

ISpec == Spec

NatOverride ==
  LET Self == Nat IN Self
====