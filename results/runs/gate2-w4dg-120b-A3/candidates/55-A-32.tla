---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

N1 == Node
I1 == initiator
R1 == R

VARIABLES parent, done, sent, echo, mint, max

vars == <<parent, done, sent, echo, mint, max>>

InitParent(n, i) == IF n = i THEN NoNode ELSE "unset"

\* The Echo module's Initialize action is duplicated exactly here so that
\* Init has the same effect as a single Echo initialization step.
Init ==
    /\ \E i \in I1 :
         /\ sent' = [n \in N1 |-> "unset"]
         /\ echo' = [n \in N1 |-> "unset"]
         /\ parent' = [n \in N1 |-> InitParent(n, i)]
         /\ done' = [n \in N1 |-> FALSE]
    /\ mint' = 1
    /\ max' = 1

\* The Echo module's SendMsg action, duplicated verbatim.
SendMsg(n, m) ==
    /\ parent[n] # "unset"
    /\ done[n]
    /\ sent[n] = "unset"
    /\ sent' = [sent EXCEPT ![n] = m]
    /\ UNCHANGED <<parent, done, echo, mint, max>>

\* The Echo module's EchoReply action, duplicated verbatim.
EchoReply(n, m) ==
    /\ sent[n] # "unset"
    /\ echo' = [echo EXCEPT ![n] = m]
    /\ UNCHANGED <<parent, done, sent, mint, max>>

\* The Echo module's Adopt action, duplicated verbatim.
Adopt(n, p) ==
    /\ echo[n] # "unset"
    /\ parent[n] = "unset"
    /\ parent' = [parent EXCEPT ![n] = p]
    /\ UNCHANGED <<done, sent, echo, mint, max>>

\* The Echo module's Finish action, duplicated verbatim.
Finish(n) ==
    /\ parent[n] # "unset"
    /\ ~done[n]
    /\ done' = [done EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<parent, sent, echo, mint, max>>

\* The Echo module's Ack action, duplicated verbatim.
Ack(n) ==
    /\ done[n]
    /\ \A p \in N1 : parent[p] = n => done[p]
    /\ done' = [n \in N1 |-> FALSE]
    /\ UNCHANGED <<parent, sent, echo, mint, max>>

Next ==
    \/ Init \/ Finish("n") \/ Ack("n")
    \/ \E n \in N1, m \in R1 : SendMsg(n, m)
    \/ \E n \in N1, p \in N1 : Adopt(n, p)
    \/ \E n \in N1, m \in R1 : EchoReply(n, m)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ parent \in [N1 -> N1 \cup {NoNode}]
    /\ done \in [N1 -> BOOLEAN]
    /\ sent \in [N1 -> R1 \cup {"unset"}]
    /\ echo \in [N1 -> R1 \cup {"unset"}]
    /\ mint \in Nat
    /\ max \in Nat

Ancestor ==
    {<<n, p>> \in N1 \X N1 :
        p # NoNode /\ (p = parent[n] \/ <<n, parent[n]>> \in Ancestor)}

AncestorProperties ==
    /\ \A n \in N1 \ {I1[[1]]} : <<n, I1[[1]]>> \in Ancestor
    /\ \A n \in N1 : <<n, n>> \notin Ancestor
    /\ \A n \in N1 : <<n, NoNode>> \notin Ancestor

TestSpec == Spec /\ TRUE

====