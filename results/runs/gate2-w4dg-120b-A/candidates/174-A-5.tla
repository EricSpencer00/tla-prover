---- MODULE Slush ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

MsgType == [src : SlushLoopProcess,
            dst : SlushQueryProcess \cup SlushLoopProcess,
            mtype : {"query", "reply", "term"},
            body : {NoMessage, NoColor} \cup Node]

\* A loop process and its node are linked through HostMapping, which ties the
\* loop, the node, and the query process together.
NodeOf(p) == CHOOSE n \in Node : \E q \in SlushQueryProcess : <<p, n, q>> \in HostMapping
QueryOf(p) == CHOOSE q \in SlushQueryProcess : <<p, NodeOf(p), q>> \in HostMapping

VARIABLES colorOf, msgs, pc, sample, iters
vars == <<colorOf, msgs, pc, sample, iters>>

TypeInvariant ==
  /\ colorOf \in [Node -> {NoColor} \union Node]
  /\ msgs \subseteq MsgType
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess \union {"SlushClient"} -> 0..2]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess \union {"SlushClient"} |-> 0]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* The client process assigns an initial color to an uncolored node.
ClientAssignsColor ==
  /\ pc["SlushClient"] = 0
  /\ \E n \in Node :
       /\ colorOf[n] = NoColor
       /\ \E c \in Node : colorOf' = [colorOf EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["SlushClient"] = 1]
  /\ UNCHANGED <<msgs, sample, iters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 0
       /\ colorOf[NodeOf(p)] # NoColor
       /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<colorOf, msgs, sample, iters>>

\* The loop process queries a random sample of peers and sends them its color.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ iters[p] < SlushIterationCount
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Q # {}
            /\ Cardinality(Q) = SampleSetSize
            /\ Q # {QueryOf(p)}
            /\ sample' = [sample EXCEPT ![p] = Q]
            /\ msgs' = msgs \union
                 {[src |-> p, dst |-> q, mtype |-> "query", body |-> colorOf[NodeOf(p)]]
                    : q \in Q]
  /\ UNCHANGED <<colorOf, pc, iters>>

RespondToQuery ==
  /\ \E q \in SlushQueryProcess :
       \E m \in msgs :
         /\ m.dst = q
         /\ m.mtype = "query"
         /\ colorOf' = IF colorOf[NodeOf(q)] = NoColor
                        THEN [colorOf EXCEPT ![NodeOf(q)] = m.body]
                        ELSE colorOf
         /\ msgs' = (msgs \ {m}) \union
                    {[src |-> q, dst |-> m.src, mtype |-> "reply",
                      body |-> IF colorOf[NodeOf(q)] = NoColor THEN m.body ELSE colorOf[NodeOf(q)]]}
         /\ UNCHANGED <<pc, sample, iters>>

\* The loop process tallies replies and adopts the majority color if it flips.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ sample[p] # {}
       /\ \A q \in sample[p] : \E m \in msgs :
            /\ m.mtype = "reply"
            /\ m.dst = p
            /\ m.src = q
       /\ LET replies == {m.body : m \in msgs /\ m.mtype = "reply" /\ m.dst = p}
              count(c) == Cardinality({m \in msgs : m.mtype = "reply" /\ m.dst = p /\ m.body = c})
              cmajor == CHOOSE c \in replies : count(c) >= PickFlipThreshold
          IN
            /\ colorOf' = [colorOf EXCEPT ![NodeOf(p)] = cmajor]
            /\ msgs' = msgs \ {m \in msgs : m.mtype = "reply" /\ m.dst = p}
            /\ sample' = [sample EXCEPT ![p] = {}]
            /\ iters' = [iters EXCEPT ![p] = @ + 1]
            /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<colorOf>>

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 2
       /\ iters[p] = SlushIterationCount
       /\ msgs' = msgs \union
            {[src |-> p, dst |-> p, mtype |-> "term", body |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<colorOf, sample, iters>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess :
       \A m \in msgs : (m.mtype = "term" /\ m.dst = p) => pc[p] = 0
  /\ \E q \in SlushQueryProcess : pc[q] = 1
       /\ pc' = [pc EXCEPT ![q] = 2]
  /\ UNCHANGED <<colorOf, msgs, sample, iters>>

Next ==
  \/ ClientAssignsColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(RespondToQuery)

Termination == <>(\A p \in SlushLoopProcess \union SlushQueryProcess : pc[p] = 2)

====