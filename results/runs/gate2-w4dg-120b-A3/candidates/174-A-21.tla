---- MODULE Slush ----
EXTENDS Integers, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

\* A host mapping is a set of triples (process, kind, node) binding each loop and
\* query process to exactly one node. This is the link the spec uses to route
\* messages between the process and the node it represents.
Hosts(k, n) == \E t \in HostMapping : t[1] = k /\ t[3] = n

Message == [to: SlushQueryProcess, tag: {"query", "qreply", "terminate"}, color: Node \cup {NoColor}]

VARIABLES colorOf, messages, pc, sample, iterations

vars == <<colorOf, messages, pc, sample, iterations>>

TypeOK ==
  /\ colorOf \in [Node -> Node \cup {NoColor}]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle", "querying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "idle"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iterations = [lp \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  /\ pc["client"] = "idle"
  /\ \E n \in Node, col \in Node :
       /\ colorOf[n] = NoColor
       /\ col # n
       /\ colorOf' = [colorOf EXCEPT ![n] = col]
  /\ pc' = [pc EXCEPT !["client"] = "done"]
  /\ UNCHANGED <<messages, sample, iterations>>

RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "idle"
       /\ pc' = [pc EXCEPT ![lp] = "querying"]
       /\ UNCHANGED <<colorOf, messages, sample, iterations>>

QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "querying"
       /\ iterations[lp] < SlushIterationCount
       /\ \E S \in SUBSET Node :
            /\ S \subseteq (Node \ { Hosts(lp, NoMessage)})
            /\ Cardinality(S) = SampleSetSize
            /\ sample' = [sample EXCEPT ![lp] = S]
            /\ messages' = messages \cup { [to |-> Hosts(lp, 2), tag |-> "query", color |-> Hosts(lp, 1)] : lp \in SlushLoopProcess }
       /\ UNCHANGED <<colorOf, pc, iterations>>

RespondToQuery ==
  /\ \E qp \in SlushQueryProcess :
       /\ \E m \in messages :
            /\ m.to = qp
            /\ m.tag = "query"
            /\ LET host == Hosts(qp, 1) IN
                 /\ colorOf' = IF colorOf[host] = NoColor THEN [colorOf EXCEPT ![host] = m.color] ELSE [colorOf EXCEPT ![host] = colorOf[host]]
            /\ messages' = (messages \ {m}) \cup { [to |-> qp, tag |-> "qreply", color |-> colorOf[Hosts(qp, 1)]] }
       /\ UNCHANGED <<pc, sample, iterations>>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ \A n \in sample[lp] :
            \E m \in messages :
              /\ m.to = Hosts(lp, 2)
              /\ m.tag = "qreply"
              /\ m.color = colorOf[n]
       /\ LET count(c) == Cardinality({n \in sample[lp] : colorOf[n] = c}) IN
            colorOf' = IF \E c \in Node : count(c) >= PickFlipThreshold THEN [colorOf EXCEPT ![Hosts(lp, 1)] = CHOOSE c \in Node : count(c) >= PickFlipThreshold] ELSE colorOf
       /\ messages' = { m \in messages : ~(m.to = Hosts(lp, 2) /\ m.tag = "qreply") }
       /\ sample' = [sample EXCEPT ![lp] = {}]
       /\ iterations' = [iterations EXCEPT ![lp] = iterations[lp] + 1]
       /\ UNCHANGED pc

LoopTermination ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "querying"
       /\ iterations[lp] = SlushIterationCount
       /\ messages' = messages \cup { [to |-> Hosts(lp, 2), tag |-> "terminate", color |-> NoColor] }
       /\ pc' = [pc EXCEPT ![lp] = "done"]
       /\ UNCHANGED <<colorOf, sample, iterations>>

QueryLoopExit ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = "idle"
       /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
       /\ pc' = [pc EXCEPT ![qp] = "done"]
       /\ UNCHANGED <<colorOf, messages, sample, iterations>>

Next ==
  \/ ClientAssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ TypeOK
  /\ \A m \in messages : m.tag \in {"query", "qreply", "terminate"}

\* The model only checks structural properties; Slush's convergence guarantee
\* is a probabilistic one and is not expressible in TLA+, so it is not verified.
====