---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, rx, sent

vars == <<correct, faulty, pc, rx, sent>>

Msgs == [snd : 1..N, kind : {"ECHO"}]

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> {"initrec", "nonrec", "sent", "accept"}]
  /\ rx \in [1..N -> SUBSET Msgs]
  /\ sent \subseteq Msgs

FCConstraints ==
  /\ correct \cup faulty = 1..N
  /\ correct \cap faulty = {}
  /\ (N > 3 * T => TRUE)
  /\ (T >= F => TRUE)
  /\ (F >= 0 => TRUE)

EchoSenders(i) == {m.snd : m \in {x \in rx[i] : x.kind = "ECHO"}}

Init ==
  /\ correct = {1, 2, 3}
  /\ faulty = {4}
  /\ pc = [i \in 1..N |-> IF i \in {1, 3} THEN "initrec" ELSE "nonrec"]
  /\ rx = [i \in 1..N |-> {}]
  /\ sent = {}

InitAllQuiet ==
  /\ correct = {1, 2, 3}
  /\ faulty = {4}
  /\ pc = [i \in 1..N |-> "nonrec"]
  /\ rx = [i \in 1..N |-> {}]
  /\ sent = {}

Receive(i) ==
  /\ pc[i] \in {"initrec", "nonrec"}
  /\ \E m \in SUBSET (sent \cup { [kind |-> "ECHO", snd |-> j] : j \in faulty }) :
       rx' = [rx EXCEPT ![i] = @ \cup m]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

InitRecAccept(i) ==
  /\ pc[i] = "initrec"
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup { [kind |-> "ECHO", snd |-> i] }
  /\ UNCHANGED <<correct, faulty, rx>>

Echogap1(i) ==
  /\ pc[i] = "nonrec"
  /\ 2 * Cardinality(EchoSenders(i)) >= N - 2 * T
  /\ Cardinality(EchoSenders(i)) < N - T
  /\ pc' = [pc EXCEPT ![i] = "sent"]
  /\ sent' = sent \cup { [kind |-> "ECHO", snd |-> i] }
  /\ UNCHANGED <<correct, faulty, rx>>

Echogap2(i) ==
  /\ pc[i] = "nonrec"
  /\ 2 * Cardinality(EchoSenders(i)) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup { [kind |-> "ECHO", snd |-> i] }
  /\ UNCHANGED <<correct, faulty, rx>>

EchoAccept(i) ==
  /\ pc[i] = "sent"
  /\ 2 * Cardinality(EchoSenders(i)) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ UNCHANGED <<correct, faulty, rx, sent>>

Next ==
  \/ \E i \in 1..N : Receive(i) \/ InitRecAccept(i) \/ Echogap1(i) \/ Echogap2(i) \/ EchoAccept(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E i \in 1..N : Receive(i))
          /\ WF_vars(\E i \in 1..N : InitRecAccept(i))
          /\ WF_vars(\E i \in 1..N : Echogap1(i))
          /\ WF_vars(\E i \in 1..N : Echogap2(i))
          /\ WF_vars(\E i \in 1..N : EchoAccept(i))

CorrLtl == (\A i \in correct : pc[i] = "initrec") ~> (\A i \in correct : pc[i] = "accept")

RelayLtl == (\E i \in correct : pc[i] = "accept") ~> (\A i \in correct : pc[i] = "accept")

UnforgLtl ==
  /\ (\A i \in correct : pc[i] # "initrec") ~> (\A i \in correct : pc[i] = "accept")
  /\ (\A i \in correct : pc[i] # "initrec") ~> (\A i \in correct : pc[i] = "accept")

====