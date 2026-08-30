---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME HostMapping \subseteq (SlushLoopProcess \cup SlushQueryProcess) \X Node

\* Each node is paired with exactly one loop process and one query process.
\* The specification treats the host mapping as a bidirectional view, which
\* is why both the domain and the range must be the full set of nodes.
NodeHosts == { n \in Node : \E lp \in SlushLoopProcess, qp \in SlushQueryProcess : <<lp, qp, n>> \in HostMapping }
LoopHosts == { n \in Node : \E lp \in SlushLoopProcess, qp \in SlushQueryProcess : <<lp, qp, n>> \in HostMapping }
QueryHosts == { n \in Node : \E lp \in SlushLoopProcess, qp \in SlushQueryProcess : <<lp, qp, n>> \in HostMapping }

\* Colors: the two Slush options plus the uncolored initial value.
Color == {0, 1}

QueryMessage(lp, qp, c) == <<lp, qp, c>>
ReplyMessage(lp, qp, c) == <<lp, qp, c>>
TerminationMessage(lp) == <<lp>>

VARIABLES
  colorOf, inbound, pc, sample, iteration

vars == <<colorOf, inbound, pc, sample, iteration>>

TypeOK ==
  /\ colorOf \in [Node -> Color \cup {NoColor}]
  /\ inbound \subseteq (SlushLoopProcess \X SlushQueryProcess \X (Color \cup {NoColor}) \cup
                        SlushLoopProcess \X {NoMessage})
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle", "waiting", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ inbound = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "idle"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iteration = [lp \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node.
AssignColor(n, c) ==
  /\ pc["client"] = "idle"
  /\ colorOf[n] = NoColor
  /\ colorOf' = [colorOf EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "assigning"]
  /\ UNCHANGED <<inbound, sample, iteration>>

CompleteAssignment ==
  /\ pc["client"] = "assigning"
  /\ pc' = [pc EXCEPT !["client"] = "idle"]
  /\ UNCHANGED <<colorOf, inbound, sample, iteration>>

RequireColor(lp) ==
  /\ pc[lp] = "idle"
  /\ colorOf[NodeHosts[lp]] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "waiting"]
  /\ UNCHANGED <<colorOf, inbound, sample, iteration>>

\* A loop process samples peers and sends a query message to each.
QueryPeers(lp, peers) ==
  /\ pc[lp] = "waiting"
  /\ sample[lp] = {}
  /\ Cardinality(peers) = SampleSetSize
  /\ peers \subseteq SlushQueryProcess
  /\ inbound' = inbound \cup {QueryMessage(lp, qp, colorOf[NodeHosts[lp]]) : qp \in peers}
  /\ sample' = [sample EXCEPT ![lp] = peers]
  /\ UNCHANGED <<colorOf, pc, iteration>>

\* A query process replies with its current color; if uncolored it adopts the query.
ReplyQuery(lp, qp) ==
  /\ pc[qp] = "idle"
  /\ \E c \in (Color \cup {NoColor}) : c # NoColor =>
       /\ colorOf' = [colorOf EXCEPT ![NodeHosts[qp]] = IF colorOf[NodeHosts[qp]] = NoColor THEN c ELSE colorOf[NodeHosts[qp]]]
       /\ inbound' = inbound \cup {ReplyMessage(lp, qp, IF colorOf[NodeHosts[qp]] = NoColor THEN c ELSE colorOf[NodeHosts[qp]])}
  /\ pc' = [pc EXCEPT ![qp] = "waiting"]
  /\ UNCHANGED <<sample, iteration>>

\* The loop process flips its node's color when a sampled color passes the flip threshold.
TallyReplies(lp) ==
  /\ pc[lp] = "waiting"
  /\ sample[lp] # {}
  /\ \A qp \in sample[lp] : \E c \in Color : ReplyMessage(lp, qp, c) \in inbound
  /\ LET votes == Cardinality({c \in Color : \E qp \in sample[lp] : ReplyMessage(lp, qp, c) \in inbound})
     IN
       \/ \E c \in Color : votes >= PickFlipThreshold /\ colorOf' = [colorOf EXCEPT ![NodeHosts[lp]] = c]
       \/ UNCHANGED colorOf
  /\ inbound' = inbound \ {m \in inbound : m[1] = lp}
  /\ sample' = [sample EXCEPT ![lp] = {}]
  /\ iteration' = [iteration EXCEPT ![lp] = iteration[lp] + 1]
  /\ pc' = IF iteration[lp] + 1 >= SlushIterationCount THEN "done" ELSE "waiting"

LoopTerminate(lp) ==
  /\ pc[lp] = "done"
  /\ inbound' = inbound \cup {TerminationMessage(lp)}
  /\ pc' = [pc EXCEPT ![lp] = "idle"]
  /\ UNCHANGED <<colorOf, sample, iteration>>

QueryLoopExit(qp) ==
  /\ pc[qp] = "waiting"
  /\ \A lp \in SlushLoopProcess : TerminationMessage(lp) \in inbound
  /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<colorOf, inbound, sample, iteration>>

Next ==
  \/ \E n \in Node, c \in Color : AssignColor(n, c)
  \/ CompleteAssignment
  \/ \E lp \in SlushLoopProcess : RequireColor(lp)
  \/ \E lp \in SlushLoopProcess, peers \in SUBSET SlushQueryProcess : QueryPeers(lp, peers)
  \/ \E lp \in SlushLoopProcess, qp \in SlushQueryProcess : ReplyQuery(lp, qp)
  \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
  \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
  \/ \E qp \in SlushQueryProcess : QueryLoopExit(qp)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(CompleteAssignment)
  /\ \A n \in Node, c \in Color : SF_vars(AssignColor(n, c))
  /\ \A lp \in SlushLoopProcess : WF_vars(RequireColor(lp))
  /\ \A lp \in SlushLoopProcess, qp \in SlushQueryProcess : SF_vars(ReplyQuery(lp, qp))
  /\ \A lp \in SlushLoopProcess : WF_vars(TallyReplies(lp))
  /\ \A qp \in SlushQueryProcess : WF_vars(QueryLoopExit(qp))

TypeInvariant == TypeOK

\* Every loop and query process eventually reaches its done state.
Termination == \A p \in (SlushLoopProcess \cup SlushQueryProcess) : <>(pc[p] = "done")

====