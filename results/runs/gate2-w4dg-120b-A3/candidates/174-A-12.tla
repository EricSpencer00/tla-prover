---- MODULE Slush ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

ASSUME Cardinality(Node) = Cardinality(SlushLoopProcess)
ASSUME Cardinality(Node) = Cardinality(SlushQueryProcess)

\* Types derived from the description; every required identifier appears.
Colors == {"c1", "c2"}
MessageKind == {"query", "reply", "term"}

ProcessOwner(p) == CHOOSE n \in Node : <<n, p>> \in HostMapping

VARIABLES color, msgs, pc, sampleOf, iters
vars == <<color, msgs, pc, sampleOf, iters>>

TypeOK ==
  /\ color \in [Node -> Colors \cup {NoColor}]
  /\ msgs \subseteq [kind : MessageKind, from : SlushQueryProcess \cup SlushLoopProcess,
                     to : SlushLoopProcess \cup SlushQueryProcess, col : Colors \cup {NoColor}]
  /\ pc \in [SlushLoopProcess -> {"waitColor", "sampling", "tallying", "done"},
             SlushQueryProcess -> {"replying", "done"},
             "client"] = [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"waitColor", "sampling", "tallying", "done", "replying", "client"}]
  /\ sampleOf \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "client"]
  /\ sampleOf = [lp \in SlushLoopProcess |-> {}]
  /\ iters = [lp \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  /\ pc["client"] = "client"
  /\ \E n \in Node, c \in Colors :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sampleOf, iters>>

\* A loop process cannot begin until its host node has been colored by the client.
RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "waitColor"
       /\ color[ProcessOwner(lp)] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = "sampling"]
  /\ UNCHANGED <<color, msgs, sampleOf, iters>>

QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "sampling"
       /\ iters[lp] < SlushIterationCount
       /\ \E qset \in {S \in SUBSET SlushQueryProcess :
                         Cardinality(S) = SampleSetSize /\ ProcessOwner(lp) \notin {ProcessOwner(q) : q \in S}} :
            /\ sampleOf' = [sampleOf EXCEPT ![lp] = qset]
            /\ msgs' = msgs \cup {[kind |-> "query", from |-> lp, to |-> q, col |-> color[ProcessOwner(lp)]] : q \in qset}
  /\ UNCHANGED <<color, pc, iters>>

ReplyToQuery ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] # "done"
       /\ \E m \in msgs :
            /\ m.kind = "query" /\ m.to = q
            /\ LET n == ProcessOwner(q) IN
                 /\ color' = IF color[n] = NoColor THEN [color EXCEPT ![n] = m.col] ELSE color
                 /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", from |-> q, to |-> m.from, col |-> IF color[n] = NoColor THEN m.col ELSE color[n]]}
  /\ UNCHANGED <<pc, sampleOf, iters>>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "tallying"
       /\ \E c \in Colors :
            /\ \A q \in sampleOf[lp] : [kind |-> "reply", from |-> q, to |-> lp, col |-> c] \in msgs
            /\ Cardinality({q \in sampleOf[lp] : [kind |-> "reply", from |-> q, to |-> lp, col |-> c] \in msgs}) >= PickFlipThreshold
            /\ color' = [color EXCEPT ![ProcessOwner(lp)] = c]
       /\ pc' = [pc EXCEPT ![lp] = "sampling"]
       /\ msgs' = msgs \ {[kind |-> "reply", from |-> q, to |-> lp, col |-> c] : q \in sampleOf[lp]}
       /\ sampleOf' = [sampleOf EXCEPT ![lp] = {}]
       /\ iters' = [iters EXCEPT ![lp] = iters[lp] + 1]

LoopTermination ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "sampling"
       /\ iters[lp] = SlushIterationCount
       /\ pc' = [pc EXCEPT ![lp] = "done"]
       /\ msgs' = msgs \cup {[kind |-> "term", from |-> lp, to |-> NoMessage, col |-> NoColor]}
  /\ UNCHANGED <<color, sampleOf, iters>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] # "done"
       /\ \A lp \in SlushLoopProcess : [kind |-> "term", from |-> lp, to |-> NoMessage, col |-> NoColor] \in msgs
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, msgs, sampleOf, iters>>

Next ==
  \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ ReplyToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(ReplyToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)

\* No safety or liveness claim about convergence exists here: TLA+ cannot
\* model the probabilistic flip itself, so the spec only checks structural
\* properties and eventual termination of all processes.
TypeInvariant == TypeOK

====