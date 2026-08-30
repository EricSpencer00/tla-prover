---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Slush is a metastable consensus protocol from the Avalanche whitepaper: a set
\* of loop processes repeatedly samples random peers and adopts a popular color.
\* TLA+ cannot model the actual coin-flip sampling, so sampling decisions are
\* left nondeterministic (any subset of the right size is possible) and the
\* client-assignment step is also nondeterministic over uncolored nodes. The
\* invariant below is purely a type check; convergence to one color is
\* probabilistic and not captured here.

MessageType == [kind: {"query", "queryReply", "termination"}, src: Node, dst: Node, color: {NoColor} \union {"c1", "c2"}]

VARIABLES colorOf, messages, pc, sample, loopCount
vars == <<colorOf, messages, pc, sample, loopCount>>

LoopActive == [pc EXCEPT ![Self] = "active"]
QueryActive == [pc EXCEPT ![Self] = "active"]

TypeInvariant ==
  /\ colorOf \in [Node -> {"c1", "c2", NoColor}]
  /\ messages \subseteq MessageType
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess -> {"ready", "waitingForColor", "active", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ loopCount \in [SlushLoopProcess -> 0..SlushIterationCount]

\* SAFETY PROPERTY (type check only; convergence is probabilistic, not TLA+ provable)
Spec == Init /\ [][Next]_vars /\ WF_vars(LoopTermination) /\ WF_vars(LoopActive) /\ WF_vars(QueryActive)

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess |-> "ready"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopCount = [p \in SlushLoopProcess |-> 0]

\* Client assigns an initial color to an uncolored node (nondeterministic choice).
AssignColor ==
  /\ \E n \in Node, c \in {"c1", "c2"} :
       /\ colorOf[n] = NoColor
       /\ colorOf' = [colorOf EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sample, loopCount>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "ready"
       /\ LET n == CHOOSE n \in Node : <<p, n>> \in HostMapping IN
            /\ colorOf[n] # NoColor
            /\ pc' = [pc EXCEPT ![p] = "active"]
  /\ UNCHANGED <<colorOf, messages, sample, loopCount>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "active"
       /\ loopCount[p] < SlushIterationCount
       /\ sample[p] = {}
       /\ LET n == CHOOSE n \in Node : <<p, n>> \in HostMapping IN
            \E s \in SUBSET (Node \ {n}) :
              /\ Cardinality(s) = SampleSetSize
              /\ sample' = [sample EXCEPT ![p] = s]
              /\ messages' = messages \union
                 {[kind |-> "query", src |-> n, dst |-> m, color |-> colorOf[n]] : m \in s}
  /\ UNCHANGED <<colorOf, pc, loopCount>>

RespondToQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query"
       /\ LET q == CHOOSE q \in SlushQueryProcess : <<q, m.dst>> \in HostMapping /\ pc[q] = "ready" IN
            /\ colorOf' = IF colorOf[m.dst] = NoColor THEN [colorOf EXCEPT ![m.dst] = m.color] ELSE colorOf
            /\ messages' = (messages \ {m}) \union
                 {[kind |-> "queryReply", src |-> m.dst, dst |-> m.src, color |-> IF colorOf[m.dst] = NoColor THEN m.color ELSE colorOf[m.dst]]}
  /\ UNCHANGED <<pc, sample, loopCount>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "active"
       /\ loopCount[p] < SlushIterationCount
       /\ sample[p] # {}
       /\ LET n == CHOOSE n \in Node : <<p, n>> \in HostMapping IN
            LET replies == {m \in messages : m.kind = "queryReply" /\ m.dst = n /\ m.src \in sample[p]} IN
              /\ replies = {m \in messages : m.kind = "queryReply" /\ m.dst = n /\ m.src \in sample[p]}
              /\ Cardinality(replies) = Cardinality(sample[p])
              /\ LET hist[c] == Cardinality({m \in replies : m.color = c}) IN
                   IF \E c \in {"c1", "c2"} : hist[c] >= PickFlipThreshold
                     THEN colorOf' = [colorOf EXCEPT ![n] = CHOOSE c \in {"c1", "c2"} : hist[c] >= PickFlipThreshold]
                     ELSE colorOf' = colorOf
              /\ messages' = messages \ {m \in replies}
              /\ sample' = [sample EXCEPT ![p] = {}]
              /\ loopCount' = [loopCount EXCEPT ![p] = @ + 1]
  /\ UNCHANGED pc

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "active"
       /\ loopCount[p] = SlushIterationCount
       /\ pc' = [pc EXCEPT ![p] = "done"]
       /\ LET n == CHOOSE n \in Node : <<p, n>> \in HostMapping IN
            messages' = messages \union {[kind |-> "termination", src |-> n, dst |-> n, color |-> NoMessage]}
  /\ UNCHANGED <<colorOf, sample, loopCount>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "ready"
       /\ (\A p \in SlushLoopProcess : pc[p] = "done")
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<colorOf, messages, sample, loopCount>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

\* Every loop process eventually reaches its done state; convergence to one
\* color is probabilistic and not LIVENESS-provable in TLA+.
LoopTermination == \A p \in SlushLoopProcess : WF_vars([][LoopActive]_vars)(p)
====