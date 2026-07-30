---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

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

\* Message types: a loop process queries a peer's query process; that process
\* replies with the peer's current color; a terminating loop process sends a
\* termination message. No probabilistic choice here -- the sample set is
\* chosen nondeterministically from the available peers.
Message == [from: SlushLoopProcess, to: SlushQueryProcess,
            kind: {"query", "queryReply", "termination"}, col: {NoColor, 1, 2}]

VARIABLES
  color, msgs, pc, sample, iterations

vars == <<color, msgs, pc, sample, iterations>>

TypeOK ==
  /\ color \in [Node -> {NoColor, 1, 2}]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> 1..2]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 1]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

ClientAssignsColor ==
  /\ pc["client"] = 1
  /\ \E n \in Node, c \in {1, 2} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sample, iterations>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ \E n \in Node : <<n, p>> \in HostMapping
       /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<color, msgs, sample, iterations>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 2
       /\ sample[p] = {}
       /\ \E s \subseteq SlushQueryProcess :
            /\ Cardinality(s) = SampleSetSize
            /\ \A q \in s : msgs' = msgs \cup {[from |-> p, to |-> q,
                                                kind |-> "query",
                                                col |-> color[CHOOSE n \in Node : <<n, p>> \in HostMapping]]}
            /\ sample' = [sample EXCEPT ![p] = s]
  /\ UNCHANGED <<color, pc, iterations>>

RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "query"
       /\ msgs' = (msgs \ {m}) \cup {[from |-> m.from, to |-> m.to,
                                     kind |-> "queryReply",
                                     col |-> IF color[CHOOSE n \in Node : <<n, m.to>> \in HostMapping] = NoColor
                                            THEN m.col
                                            ELSE color[CHOOSE n \in Node : <<n, m.to>> \in HostMapping]]}
       /\ color' = [n \in Node |-> IF <<n, m.to>> \in HostMapping /\ color[n] = NoColor
                                   THEN m.col ELSE color[n]]
  /\ UNCHANGED <<pc, sample, iterations>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ sample[p] # {}
       /\ \A q \in sample[p] : \E _ \in msgs : _ = [from |-> p, to |-> q, kind |-> "queryReply", col |-> 1]
       /\ \E oneCount \in 0..SampleSetSize, twoCount \in 0..SampleSetSize :
            /\ oneCount + twoCount = SampleSetSize
            /\ (oneCount >= PickFlipThreshold => color' = [color EXCEPT ![CHOOSE n \in Node : <<n, p>> \in HostMapping] = 1])
            /\ (twoCount >= PickFlipThreshold => color' = [color EXCEPT ![CHOOSE n \in Node : <<n, p>> \in HostMapping] = 2])
       /\ msgs' = msgs \ {[from |-> p, to |-> q, kind |-> "queryReply", col |-> 1] : q \in sample[p]}
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
       /\ UNCHANGED pc

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ iterations[p] = SlushIterationCount
       /\ msgs' = msgs \cup {[from |-> p, to |-> m, kind |-> "termination", col |-> NoColor] : m \in SlushLoopProcess}
       /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<color, sample, iterations>>

QueryLoopExit ==
  /\ \A m \in msgs : m.kind = "termination" => m.from \in SlushLoopProcess
  /\ \A q \in SlushQueryProcess :
       /\ \E m \in msgs : m.kind = "termination" /\ m.from = CHOOSE p \in SlushLoopProcess : <<n, p>> \in HostMapping
  /\ UNCHANGED <<color, msgs, pc, sample, iterations>>

Next == ClientAssignsColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
        /\ SF_vars(LoopTermination) /\ SF_vars(QueryLoopExit)

TypeInvariant == TypeOK

====