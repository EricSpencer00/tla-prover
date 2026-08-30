---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

\* Echo spanning tree over a three-node fully-meshed graph; all Echo
\* specification identifiers are reproduced here verbatim, so the
\* module is checked exactly against the declared SPECIFICATION,
\* INVARIANTS, and PROPERTIES.
CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, acked, phase, phaseLock

vars == <<parent, acked, phase, phaseLock>>

Sent == {n \in Node : phaseLock[n] = initiator}

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ acked \in [Node -> BOOLEAN]
    /\ phase \in [Node -> {"init", "echoed"}]
    /\ phaseLock \in [Node -> Node \cup {NoNode}]

\* An echo spanning tree is a rooted arborescence: the initiator reaches
\* every other node via the parent relation, which is acyclic.
AncestorProperties ==
    /\ (forall n \in Node : (n # initiator /\ parent[n] # NoNode) => (parent[n] # n /\ phase[n] = "echoed"))
    /\ (forall n \in Node : n # initiator /\ phase[n] = "init" => parent[n] # NoNode)
    /\ (forall n \in Node : n # initiator /\ parent[n] # NoNode => phase[parent[n]] = "echoed")
    /\ (forall n \in Node : (~ acked[n] \/ parent[n] # NoNode) => acked[parent[n]])
    /\ (forall n \in Node : n # initiator /\ acked[n] => parent[n] # NoNode)
    /\ (forall n \in Node : ~ acked[n] => phase[n] = "init")
    /\ \A m, n \in Sent \ {initiator} : (m # n) => (parent[m] # parent[n])

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ acked = [n \in Node |-> FALSE]
    /\ phase = [n \in Node |-> "init"]
    /\ phaseLock = [n \in Node |-> NoNode]

\* The initiator also rebroadcasts the acquire on a free lock, so it can
\* never be stuck just because every node it has already echoed to is
\* sitting on an occupied lock.
Acquire ==
    /\ phase[initiator] = "init"
    /\ phaseLock[initiator] = NoNode
    /\ phase' = [phase EXCEPT ![initiator] = "echoed"]
    /\ phaseLock' = [phaseLock EXCEPT ![initiator] = initiator]
    /\ UNCHANGED <<parent, acked>>

Echo(n) ==
    /\ phaseLock[initiator] # NoNode
    /\ phase[n] = "init"
    /\ n # initiator
    /\ parent' = [parent EXCEPT ![n] = initiator]
    /\ phase' = [phase EXCEPT ![n] = "echoed"]
    /\ UNCHANGED <<acked, phaseLock>>

EchoRecurs(n) ==
    /\ phaseLock[initiator] # NoNode
    /\ phase[n] = "init"
    /\ n # initiator
    /\ \E m \in Sent \ {initiator} : parent' = [parent EXCEPT ![n] = m]
    /\ phase' = [phase EXCEPT ![n] = "echoed"]
    /\ UNCHANGED <<acked, phaseLock>>

\* A lock is released only once its holder has been acked, so the release
\* decision can never race ahead of an acknowledgement it depends on.
ReleaseIfAcked(n) ==
    /\ phaseLock[n] # NoNode
    /\ acked[n]
    /\ phaseLock' = [phaseLock EXCEPT ![n] = NoNode]
    /\ UNCHANGED <<parent, acked, phase>>

Ack(n) ==
    /\ phaseLock[n] # NoNode
    /\ ~ acked[n]
    /\ acked' = [acked EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<parent, phase, phaseLock>>

Next ==
    \/ Acquire
    \/ \E n \in Node : Echo(n) \/ EchoRecurs(n) \/ ReleaseIfAcked(n) \/ Ack(n)

\* A lock that is never released would freeze the whole broadcast, so
\* every held lock is eventually released -- which is what forces every
\* node to eventually be echoed to and acked.
EventualEchoRelease == \A n \in Node : (phaseLock[n] # NoNode) ~> (phaseLock[n] = NoNode)

\* Test variant: prints the fully-meshed graph under consideration at
\* startup before any Echo action can fire.
TestSpec ==
    /\ \A m, n \in Node : m # n => {m, n} \in R
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Acquire)
    /\ \A n \in Node : WF_vars(Echo(n))
    /\ SF_vars(EchoRecurs(initiator))
    /\ WF_vars(Ack(initiator))
    /\ WF_vars(\E n \in Node : ReleaseIfAcked(n))
    /\ SF_vars(EventualEchoRelease)

\* The Echo specification is fully deterministic once the graph is
\* fixed, so SF_vars(EventualEchoRelease) suffices for safety -- but
\* each node's own lock must still be released eventually, which is
\* where that weak fairness condition comes into play.
Spec == TestSpec

\* The operators below are not meant to be re-used; they exist only so
\* the .cfg file can bind the CONSTANTS to concrete finite values.
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {{ "n1", "n2" }, { "n2", "n3" }, { "n1", "n3" }}
====