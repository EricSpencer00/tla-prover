---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Message == {"ECHO"}

VARIABLES correct, faulty, state, rcv, sent
vars == <<correct, faulty, state, rcv, sent>>

RECURSIVE SetOf(_, _)
SetOf(f, S) == IF S = {} THEN {}
              ELSE LET x == CHOOSE y \in S : TRUE
                   IN {f[x]} \cup SetOf(f, S \ {x})

Locs == {"receivedInit", "noInit", "sentEcho", "accepted"}
Onfty == 255

TypeOK ==
  /\ correct \subseteq (0..(N-1))
  /\ faulty = (0..(N-1)) \ correct
  /\ state \in [0..(N-1) -> Locs]
  /\ rcv \in [0..(N-1) -> SUBSET ((0..(N-1)) \times Message)]
  /\ sent \subseteq ((0..(N-1)) \times Message)

FCConstraints ==
  /\ N > 3 * T
  /\ F <= T
  /\ F >= 0

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (0..(N-1)) \ correct
  /\ \E S \in SetOf(g \in 0..(N-1) : {"receivedInit", "noInit"} : g) :
        state = S
  /\ rcv = [p \in 0..(N-1) |-> {}]
  /\ sent = {}

Receive(p) ==
  /\ p \in correct
  /\ ~ state[p] \in {"sentEcho", "accepted"}
  /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup (sent \cup
               SetOf(g \in 0..(N-1) : {g, "ECHO"} : g))]
  /\ UNCHANGED <<correct, faulty, state, sent>>

SendEcho(p) ==
  /\ p \in correct
  /\ state[p] \in {"receivedInit"}
  /\ state' = [state EXCEPT ![p] = "sentEcho"]
  /\ sent' = sent \cup {p, "ECHO"}
  /\ UNCHANGED <<correct, faulty, rcv>>

StrongEcho(p) ==
  /\ p \in correct
  /\ state[p] # "receivedInit"
  /\ ~ state[p] \in {"sentEcho", "accepted"}
  /\ Cardinality({q \in 0..(N-1) : {q, "ECHO"} \in rcv[p]}) >= N - T
  /\ state' = [state EXCEPT ![p] = "sentEcho"]
  /\ sent' = sent \cup {p, "ECHO"}
  /\ UNCHANGED <<correct, faulty, rcv>>

WeakEcho(p) ==
  /\ p \in correct
  /\ state[p] # "receivedInit"
  /\ ~ state[p] \in {"sentEcho", "accepted"}
  /\ Cardinality({q \in 0..(N-1) : {q, "ECHO"} \in rcv[p]}) >= N - 2 * T
  /\ Cardinality({q \in 0..(N-1) : {q, "ECHO"} \in rcv[p]}) < N - T
  /\ state' = [state EXCEPT ![p] = "sentEcho"]
  /\ sent' = sent \cup {p, "ECHO"}
  /\ UNCHANGED <<correct, faulty, rcv>>

Accept(p) ==
  /\ p \in correct
  /\ ~ state[p] \in {"accepted"}
  /\ Cardinality({q \in 0..(N-1) : {q, "ECHO"} \in rcv[p]}) >= N - T
  /\ state' = [state EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, rcv, sent>>

Next ==
  \/ \E p \in 0..(N-1) : Receive(p)
  \/ \E p \in 0..(N-1) : SendEcho(p)
  \/ \E p \in 0..(N-1) : StrongEcho(p)
  \/ \E p \in 0..(N-1) : WeakEcho(p)
  \/ \E p \in 0..(N-1) : Accept(p)

Spec ==
  /\ Init
  /\ TRUE
  /\ [][Next]_vars
  /\ \A p \in 0..(N-1) : (p \in correct /\ state[p] \in {"sentEcho", "accepted"}) ~> (state[p] = "accepted")
  /\ \A p \in 0..(N-1) : (p \in correct /\ state[p] = "receivedInit") ~> (state[p] = "accepted")

CorrLtl == (\A p \in 0..(N-1) : p \in correct => state[p] = "receivedInit") ~> (\A p \in 0..(N-1) : p \in correct => state[p] = "accepted")
RelayLtl == (\E p \in 0..(N-1) : p \in correct /\ state[p] = "accepted") ~> (\A p \in 0..(N-1) : p \in correct => state[p] = "accepted")
UnforgLtl == (\A p \in 0..(N-1) : correct => state[p] # "receivedInit") ~> (\A p \in 0..(N-1) : p \in correct => state[p] # "accepted")
====