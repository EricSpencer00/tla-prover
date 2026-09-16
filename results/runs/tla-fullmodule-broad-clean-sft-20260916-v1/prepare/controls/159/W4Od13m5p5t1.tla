---- MODULE W4Od13m5p5t1 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Machines, Proposals, QuorumSize

VARIABLES sent, delivered, executed, quorumWitness

vars == <<sent, delivered, executed, quorumWitness>>

TypeOK ==
  /\ sent \subseteq (Machines \X Proposals)
  /\ delivered \subseteq (Machines \X Proposals)
  /\ executed \subseteq Proposals
  /\ quorumWitness \in [Proposals -> SUBSET Machines]

Init ==
  /\ sent = {}
  /\ delivered = {}
  /\ executed = {}
  /\ quorumWitness = [p \in Proposals |-> {}]

SendVote(m, p) ==
  /\ <<m, p>> \notin sent
  /\ sent' = sent \cup {<<m, p>>}
  /\ UNCHANGED <<delivered, executed, quorumWitness>>

Deliver(m, p) ==
  /\ <<m, p>> \in sent
  /\ <<m, p>> \notin delivered
  /\ delivered' = delivered \cup {<<m, p>>}
  /\ UNCHANGED <<sent, executed, quorumWitness>>

Execute(p) ==
  /\ p \notin executed
  /\ Cardinality({m \in Machines : <<m, p>> \in delivered}) >= QuorumSize
  /\ executed' = executed \cup {p}
  /\ quorumWitness' = [quorumWitness EXCEPT ![p] = {m \in Machines : <<m, p>> \in delivered}]
  /\ UNCHANGED <<sent, delivered>>

Withdraw(m, p) ==
  /\ p \notin executed
  /\ <<m, p>> \in sent
  /\ sent' = sent \ {<<m, p>>}
  /\ delivered' = delivered \ {<<m, p>>}
  /\ UNCHANGED <<executed, quorumWitness>>

Idle == UNCHANGED vars

Next ==
  \/ \E m \in Machines, p \in Proposals : SendVote(m, p)
  \/ \E m \in Machines, p \in Proposals : Deliver(m, p)
  \/ \E p \in Proposals : Execute(p)
  \/ \E m \in Machines, p \in Proposals : Withdraw(m, p)
  \/ Idle

Spec == Init /\ [][Next]_vars

AtMostOnceByQuorum ==
  \A p \in Proposals :
    p \in executed =>
      /\ Cardinality(quorumWitness[p]) >= QuorumSize
      /\ quorumWitness[p] \subseteq {m \in Machines : <<m, p>> \in delivered}

====
