---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, discoveries, phase, recvLog

vars == <<parent, discoveries, phase, recvLog>>

RECURSIVE Trail(_)
Trail(n) == IF n = NoNode THEN {} ELSE {n} \cup Trail(parent[n])

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ discoveries \subseteq Node
  /\ phase \in [Node -> {"idle", "waiting", "done"}]
  /\ recvLog \subseteq (Node \X Node)

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE initiator]
  /\ discoveries = {initiator}
  /\ phase = [n \in Node |-> IF n = initiator THEN "waiting" ELSE "idle"]
  /\ recvLog = {}

Transmit(n, m) ==
  /\ n # m
  /\ <<n, m>> \in R
  /\ n \in discoveries
  /\ phase[m] = "idle"
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ phase' = [phase EXCEPT ![m] = "waiting"]
  /\ UNCHANGED <<discoveries, recvLog>>

Echo(m) ==
  /\ phase[m] = "waiting"
  /\ m \in discoveries
  /\ phase' = [phase EXCEPT ![m] = "done"]
  /\ UNCHANGED <<parent, discoveries, recvLog>>

Discover(n) ==
  /\ n \notin discoveries
  /\ \E b \in Node : <<parent[n], n>> \in recvLog /\ b \in discoveries
  /\ discoveries' = discoveries \cup {n}
  /\ recvLog' = recvLog \cup {<<parent[n], n>>}
  /\ UNCHANGED <<parent, phase>>

Next == (\E n \in Node : Discover(n))
        \/ (\E n \in Node : \E m \in Node : Transmit(n, m))
        \/ (\E n \in Node : Echo(n))

PrintState ==
  /\ UNCHANGED vars
  /\ PrintT("R = {")
  /\ \E a \in Node :
       /\ PrintT("\t")
       /\ PrintT(a)
       /\ PrintT(" : {")
       /\ \E b \in Node :
            /\ IF a = b THEN UNCHANGED vars
            ELSE IF b \in Node /\ <<a, b>> \in R THEN PrintT(b)
            ELSE PrintT("none")
            /\ IF b # CHOOSE x \in Node : TRUE THEN PrintT(", ") ELSE UNCHANGED vars
            /\ UNCHANGED vars
       /\ PrintT("}")
       /\ IF a # CHOOSE x \in Node : TRUE THEN PrintT(",") ELSE PrintT("}")
       /\ UNCHANGED vars
  /\ PrintT("\n")

Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ PrintState

AncestorProperties ==
  /\ (CHOOSE n \in Node : phase[n] = "waiting") \in discoveries
  /\ (CHOOSE n \in Node : phase[n] = "waiting") \notin Trail(NoNode)
  /\ \A n \in Node \ {CHOOSE n \in Node : phase[n] = "waiting"} : n \in Trail(NoNode)

====