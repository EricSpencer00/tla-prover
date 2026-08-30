---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* A host mapping ties each node to its loop process and its query process.
\* The two process families share one message set, so replies and queries
\* interleave arbitrarily -- this is where the network's asynchrony lives.
\* The loop process only flips its node's color once a sampled majority
\* (the flip threshold) of replies agrees on a color.

VARIABLES
  color, msgs, pc, sample, iteration

vars == <<color, msgs, pc, sample, iteration>>

\* Message types: a query from a loop process, a reply to a loop process,
\* and a termination broadcast once a loop process is done.
Message == [kind: {"query", "reply", "termination"},
            src: SlushLoopProcess \cup SlushQueryProcess,
            dst: SlushLoopProcess \cup SlushQueryProcess,
            col: {NoColor} \cup {"red", "blue"}]

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup {"red", "blue"}]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"waiting", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess |-> "waiting"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node; this is the
\* only way a node ever gets a color, so it must keep firing until all
\* nodes are colored.
AssignColor ==
  /\ \E n \in Node, c \in {"red", "blue"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sample, iteration>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waiting"
       /\ LET n == CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping
          IN /\ color[n] # NoColor
             /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<color, msgs, sample, iteration>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sampling"
       /\ sample[p] = {}
       /\ LET n == CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping
          IN /\ \E Q \in SUBSET SlushQueryProcess :
                /\ Cardinality(Q) = SampleSetSize
                /\ \A q \in Q : msgs' = msgs \cup
                     {[kind |-> "query", src |-> p, dst |-> q, col |-> color[n]]}
                /\ sample' = [sample EXCEPT ![p] = Q]
          /\ pc' = [pc EXCEPT ![p] = "tallying"]
  /\ UNCHANGED <<color, iteration>>

RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "query"
       /\ LET n == CHOOSE n \in Node : <<n, m.dst, NoMessage>> \in HostMapping
          IN /\ color' = [color EXCEPT ![n] =
                            IF color[n] = NoColor THEN m.col ELSE color[n]]
             /\ msgs' = (msgs \ {m}) \cup
                  {[kind |-> "reply", src |-> m.dst, dst |-> m.src, col |-> color[n]]}
  /\ UNCHANGED <<pc, sample, iteration>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "tallying"
       /\ \A q \in sample[p] : \E m \in msgs :
            /\ m.kind = "reply" /\ m.dst = p /\ m.src = q
            /\ msgs' = msgs \ {m}
       /\ LET n == CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping
              redCount == Cardinality({q \in sample[p] :
                [kind |-> "reply", src |-> q, dst |-> p, col |-> "red"] \in msgs})
              blueCount == Cardinality({q \in sample[p] :
                [kind |-> "reply", src |-> q, dst |-> p, col |-> "blue"] \in msgs})
              newColor == IF redCount >= PickFlipThreshold THEN "red"
                          ELSE IF blueCount >= PickFlipThreshold THEN "blue"
                          ELSE color[n]
          IN /\ color' = [color EXCEPT ![n] = newColor]
             /\ sample' = [sample EXCEPT ![p] = {}]
             /\ iteration' = [iteration EXCEPT ![p] =
                                IF iteration[p] < SlushIterationCount
                                THEN iteration[p] + 1 ELSE iteration[p]]
             /\ pc' = IF iteration[p] < SlushIterationCount
                      THEN "sampling" ELSE "done"
  /\ UNCHANGED msgs

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ msgs' = msgs \cup
            {[kind |-> "termination", src |-> p, dst |-> NoMessage, col |-> NoColor]}
  /\ UNCHANGED <<color, pc, sample, iteration>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \A q \in SlushQueryProcess :
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, msgs, sample, iteration>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
  /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
  /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
  /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done"

====