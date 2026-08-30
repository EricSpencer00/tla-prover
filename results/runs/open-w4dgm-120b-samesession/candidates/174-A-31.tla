---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Two colors for the binary decision; NoColor means uncolored (admitted but undecided).
Color == {NoColor} \cup {"blue", "green"}
Message == [kind: {"query", "reply", "done"}, src: SlushQueryProcess, dst: SlushLoopProcess, col: Color]

VARIABLES nodeColor, messages, pc, sampleSet, iterations

vars == <<nodeColor, messages, pc, sampleSet, iterations>>

TypeOK ==
  /\ nodeColor \in [Node -> Color]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"waitingColor", "sampling", "tallying", "done"}]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess |-> "waitingColor"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to some uncolored node; this repeats until
\* every node has a color -- the "admitted" part of the pool.
ClientAssignsColor ==
  \E n \in Node, c \in {"blue", "green"} :
    /\ nodeColor[n] = NoColor
    /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sampleSet, iterations>>

RequireColor ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "waitingColor"
    /\ \E n \in Node :
         /\ <<n, p, NoMessage>> \in HostMapping
         /\ nodeColor[n] # NoColor
         /\ pc' = [pc EXCEPT ![p] = "sampling"]
    /\ UNCHANGED <<nodeColor, messages, sampleSet, iterations>>

\* A loop process samples a fixed-size random subset of other nodes and queries
\* each sampled peer's color.
QuerySampleSet ==
  \E p \in SlushLoopProcess :
    /\ pc[p] = "sampling"
    /\ sampleSet[p] = {}
    /\ sampleSet' = [sampleSet EXCEPT ![p] = CHOOSE s \in SUBSET (SlushQueryProcess \ {{p}}) :
                                        Cardinality(s) = SampleSetSize]
    /\ pc' = [pc EXCEPT ![p] = "tallying"]
    /\ messages' = messages \cup
         { [kind |-> "query", src |-> q, dst |-> p, col |-> nodeColor[CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping]] : q \in sampleSet[p] }
    /\ UNCHANGED <<nodeColor, iterations>>

RespondToQuery ==
  \E m \in messages :
    /\ m.kind = "query"
    /\ LET n == CHOOSE n \in Node : <<n, m.dst, NoMessage>> \in HostMapping IN
         /\ nodeColor' = [nodeColor EXCEPT ![n] =
                          IF nodeColor[n] = NoColor THEN m.col ELSE nodeColor[n]]
         /\ m' = [m EXCEPT !.col = nodeColor[CHOOSE n \in Node : <<n, m.dst, NoMessage>> \in HostMapping]]
    /\ messages' = (messages \ {m}) \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, col |-> m.col]}
    /\ UNCHANGED <<pc, sampleSet, iterations>>

\* The loop process flips its color only when a supermajority of the sampled
\* replies agree on one color; otherwise it keeps its current color.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "tallying"
       /\ Cardinality({m \in messages : m.kind = "reply" /\ m.dst = p}) = SampleSetSize
       /\ LET pool == {m \in messages : m.kind = "reply" /\ m.dst = p}
              tally(c) == Cardinality({m \in pool : m.col = c}) IN
            nodeColor' = IF \E c \in {"blue", "green"} : tally(c) >= PickFlipThreshold
                          THEN [n \in Node |-> IF <<n, p, NoMessage>> \in HostMapping
                                                THEN CHOOSE c \in {"blue", "green"} : tally(c) >= PickFlipThreshold
                                                ELSE nodeColor[n]]
                          ELSE nodeColor
       /\ messages' = {m \in messages : m.kind # "reply" \/ m.dst # p}
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ pc' = IF iterations[p] + 1 >= SlushIterationCount THEN "done" ELSE "waitingColor"
       /\ iterations' = [iterations EXCEPT ![p] = IF iterations[p] + 1 >= SlushIterationCount
                                                   THEN SlushIterationCount ELSE iterations[p] + 1]

LoopTermination ==
  /\ \E p \in SlushLoopProcess : pc[p] = "done" /\ messages' = messages \cup {[kind |-> "done", src |-> NoMessage, dst |-> p, col |-> NoColor]}
  /\ UNCHANGED <<nodeColor, pc, sampleSet, iterations>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \A q \in SlushQueryProcess : pc[q] = "done"
  /\ UNCHANGED vars

Next == ClientAssignsColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] = "done")

====