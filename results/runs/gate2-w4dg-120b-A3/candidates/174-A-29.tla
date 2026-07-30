---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess,
  HostMapping, SlushIterationCount,
  SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

ASSUME /\ HostMapping \subseteq (SlushLoopProcess \X SlushQueryProcess \X Node)
         /\ Cardinality(HostMapping) = Cardinality(SlushLoopProcess)
         /\ \A n \in SlushLoopProcess : \E p \in SlushQueryProcess, nd \in Node : <<n, p, nd>> \in HostMapping
         /\ SlushIterationCount \in Nat /\ SlushIterationCount > 0
         /\ SampleSetSize \in Nat /\ SampleSetSize > 0
         /\ PickFlipThreshold \in Nat /\ PickFlipThreshold > 0

ProcN(n) == CHOOSE nd \in Node : <<n, CHOOSE p \in SlushQueryProcess : <<n, p, nd>> \in HostMapping, nd>> \in HostMapping
QueryN(p) == CHOOSE nd \in Node : \E n \in SlushLoopProcess : <<n, p, nd>> \in HostMapping

MessageTypes == {"query", "queryReply", "termination"}

VARIABLES nodeColor, msgs, pc, sampleSet, curIter

vars == <<nodeColor, msgs, pc, sampleSet, curIter>>

Message == [t \in MessageTypes, src \in Node, dst \in Node, col : Node \cup {NoColor}]

TypeOK ==
  /\ nodeColor \in [Node -> Node \cup {NoColor}]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"clientRequest"} -> {"waiting", "active", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ curIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"clientRequest"}) |-> "waiting"]
  /\ sampleSet = [n \in SlushLoopProcess |-> {}]
  /\ curIter = [n \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ pc["clientRequest"] = "waiting"
  /\ \E nd \in Node, c \in Node \ {NoColor} :
       /\ nodeColor[nd] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![nd] = c]
  /\ pc' = [pc EXCEPT !["clientRequest"] = "waiting"]
  /\ UNCHANGED <<msgs, sampleSet, curIter>>

RequireColor ==
  /\ \E n \in SlushLoopProcess :
       /\ pc[n] = "waiting"
       /\ nodeColor[ProcN(n)] # NoColor
       /\ pc' = [pc EXCEPT ![n] = "active"]
  /\ UNCHANGED <<nodeColor, msgs, sampleSet, curIter>>

QuerySampleSet ==
  /\ \E n \in SlushLoopProcess :
       /\ pc[n] = "active"
       /\ curIter[n] < SlushIterationCount
       /\ sampleSet[n] = {}
       /\ \E s \in SUBSET SlushQueryProcess :
            /\ Cardinality(s) = SampleSetSize
            /\ sampleSet' = [sampleSet EXCEPT ![n] = s]
            /\ msgs' = msgs \cup {[t |-> "query", src |-> ProcN(n), dst |-> QueryN(p), col |-> nodeColor[ProcN(n)]] : p \in s}
  /\ UNCHANGED <<nodeColor, pc, curIter>>

RespondToQuery ==
  /\ \E p \in SlushQueryProcess :
       /\ \E m \in msgs :
            /\ m.t = "query"
            /\ m.dst = QueryN(p)
            /\ nodeColor' = IF nodeColor[QueryN(p)] = NoColor THEN [nodeColor EXCEPT ![QueryN(p)] = m.col] ELSE nodeColor
            /\ msgs' = (msgs \ {m}) \cup {[t |-> "queryReply", src |-> QueryN(p), dst |-> m.src, col |-> nodeColor[QueryN(p)]]}
  /\ UNCHANGED <<pc, sampleSet, curIter>>

TallyReplies ==
  /\ \E n \in SlushLoopProcess :
       /\ sampleSet[n] # {}
       /\ \A p \in sampleSet[n] : \E m \in msgs : m.t = "queryReply" /\ m.src = QueryN(p) /\ m.dst = ProcN(n)
       /\ LET nreplies == {m \in msgs : m.t = "queryReply" /\ m.dst = ProcN(n)}
              cnt(c) == Cardinality({m \in nreplies : m.col = c})
          IN nodeColor' = IF \E c \in Node \ {NoColor} : cnt(c) >= PickFlipThreshold
                            THEN [nodeColor EXCEPT ![ProcN(n)] = CHOOSE c \in Node \ {NoColor} : cnt(c) >= PickFlipThreshold]
                            ELSE nodeColor
       /\ msgs' = msgs \ {m \in msgs : m.t = "queryReply" /\ m.dst = ProcN(n)}
       /\ sampleSet' = [sampleSet EXCEPT ![n] = {}]
       /\ curIter' = [curIter EXCEPT ![n] = @ + 1]
  /\ UNCHANGED pc

LoopTermination ==
  /\ \E n \in SlushLoopProcess :
       /\ pc[n] = "active"
       /\ curIter[n] >= SlushIterationCount
       /\ msgs' = msgs \cup {[t |-> "termination", src |-> ProcN(n), dst |-> NoMessage, col |-> NoColor]}
       /\ pc' = [pc EXCEPT ![n] = "done"]
  /\ UNCHANGED <<nodeColor, sampleSet, curIter>>

QueryLoopExit ==
  /\ \E p \in SlushQueryProcess :
       /\ pc[p] = "waiting"
       /\ \A m \in msgs : m.t = "termination"
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<nodeColor, msgs, sampleSet, curIter>>

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

Termination ==
  \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"clientRequest"}) : pc[p] = "done"

====