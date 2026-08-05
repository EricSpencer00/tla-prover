---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

SlushProcess == SlushLoopProcess \cup SlushQueryProcess

VARIABLES color, messages, loopPC, queryPC, sampleSet, loopIteration

vars == <<color, messages, loopPC, queryPC, sampleSet, loopIteration>>

\* Loop processes drive the Slush iteration; query processes only answer incoming
\* queries. All messages travel over a single shared mailbox, and a query reply
\* is only ever generated in response to a query message already in that mailbox.
Message == [kind: {"query", "queryReply", "termination"},
             to: SlushProcess, from: SlushProcess, col: 0..2]

RECURSIVE Tally(_, _)
Tally(S, c) ==
    IF S = {} THEN 0
    ELSE LET m == CHOOSE x \in S : TRUE
         IN (IF m.col = c THEN 1 ELSE 0) + Tally(S \ {m}, c)

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ loopPC = [lp \in SlushLoopProcess |-> "waitingForColor"]
    /\ queryPC = [qp \in SlushQueryProcess |-> "replyLoop"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ loopIteration = [lp \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (a transaction).
ClientAssignsColor ==
    /\ \E n \in Node :
         /\ color[n] = NoColor
         /\ \E c \in {1, 2} : color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, loopPC, queryPC, sampleSet, loopIteration>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ loopPC[lp] = "waitingForColor"
         /\ \E n \in Node :
              /\ <<SlushLoopProcess, SlushQueryProcess>> \notin HostMapping
              /\ n \in HostMapping[SlushLoopProcess, SlushQueryProcess, lp]
              /\ color[n] # NoColor
              /\ loopPC' = [loopPC EXCEPT ![lp] = "querying"]
    /\ UNCHANGED <<color, messages, queryPC, sampleSet, loopIteration>>

\* A loop process picks a random fixed-size sample of peers to query.
QuerySampleSet ==
    /\ \E lp \in SlushLoopProcess :
         /\ loopPC[lp] = "querying"
         /\ \E peers \in (SlushQueryProcess \ {lp}) :
              /\ Cardinality(peers) = SampleSetSize
              /\ messages' = messages \cup { [kind |-> "query",
                       to |-> qp,
                       from |-> lp,
                       col |-> color[CHOOSE n \in Node :
                            <<SlushLoopProcess, SlushQueryProcess, lp, qp>> \in HostMapping]) : qp \in peers })
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
    /\ UNCHANGED <<color, loopPC, queryPC, loopIteration>>

RespondToQuery ==
    /\ \E qp \in SlushQueryProcess :
         /\ \E m \in messages :
              /\ m.kind = "query"
              /\ m.to = qp
              /\ color' = [color EXCEPT ![CHOOSE n \in Node :
                    <<SlushLoopProcess, SlushQueryProcess, m.from, qp>> \in HostMapping] =
                      IF color[CHOOSE n \in Node :
                            <<SlushLoopProcess, SlushQueryProcess, m.from, qp>> \in HostMapping] = NoColor
                      THEN m.col
                      ELSE color[CHOOSE n \in Node :
                            <<SlushLoopProcess, SlushQueryProcess, m.from, qp>> \in HostMapping]]
              /\ messages' = (messages \ {m}) \cup
                      {[kind |-> "queryReply", to |-> m.from, from |-> qp, col |-> color[CHOOSE n \in Node :
                          <<SlushLoopProcess, SlushQueryProcess, m.from, qp>> \in HostMapping]]}
    /\ UNCHANGED <<loopPC, queryPC, sampleSet, loopIteration>>

\* Once a loop process has collected replies from its whole sample, it may adopt
\* whichever color reaches the flip threshold in this round.
TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
         /\ loopPC[lp] = "querying"
         /\ sampleSet[lp] # {}
         /\ \A qp \in sampleSet[lp] : \E m \in messages : m.kind = "queryReply" /\ m.to = lp /\ m.from = qp
         /\ IF Tally({m \in messages :
                 /\ m.kind = "queryReply"
                 /\ m.to = lp
                 /\ m.from \in sampleSet[lp]}, 1) >= PickFlipThreshold
             THEN color' = [color EXCEPT ![CHOOSE n \in Node :
                        <<SlushLoopProcess, SlushQueryProcess, lp, CHOOSE qp \in sampleSet[lp] : TRUE>> \in HostMapping] = 1]
             ELSE IF Tally({m \in messages :
                 /\ m.kind = "queryReply"
                 /\ m.to = lp
                 /\ m.from \in sampleSet[lp]}, 2) >= PickFlipThreshold
                  THEN color' = [color EXCEPT ![CHOOSE n \in Node :
                        <<SlushLoopProcess, SlushQueryProcess, lp, CHOOSE qp \in sampleSet[lp] : TRUE>> \in HostMapping] = 2]
                  ELSE color
         /\ messages' = {m \in messages : ~(m.kind = "queryReply" /\ m.to = lp /\ m.from \in sampleSet[lp])}
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
         /\ loopIteration' = [loopIteration EXCEPT ![lp] = @ + 1]
         /\ loopPC' = [loopPC EXCEPT ![lp] = "querying"]
    /\ UNCHANGED <<queryPC>>

LoopTermination ==
    /\ \E lp \in SlushLoopProcess :
         /\ loopPC[lp] # "done"
         /\ loopIteration[lp] >= SlushIterationCount
         /\ messages' = messages \cup {[kind |-> "termination", to |-> lp, from |-> NoMessage, col |-> 0]}
         /\ loopPC' = [loopPC EXCEPT ![lp] = "done"]
    /\ UNCHANGED <<color, queryPC, sampleSet, loopIteration>>

QueryLoopExit ==
    /\ \E qp \in SlushQueryProcess :
         /\ queryPC[qp] # "exit"
         /\ \A lp \in SlushLoopProcess : \A m \in messages :
              ~(m.kind = "termination" /\ m.to = lp)
         /\ queryPC' = [queryPC EXCEPT ![qp] = "exit"]
    /\ UNCHANGED <<color, messages, loopPC, sampleSet, loopIteration>>

Next ==
    \/ ClientAssignsColor \/ RequireColor \/ QuerySampleSet
    \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
    /\ WF_vars(ClientAssignsColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
    /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)
    /\ WF_vars(QueryLoopExit)

TypeInvariant ==
    /\ color \in [Node -> 0..2]
    /\ messages \subseteq Message

AllProcessesEventuallyDone ==
    \A lp \in SlushLoopProcess : <>(loopPC[lp] = "done")
        /\ \A qp \in SlushQueryProcess : <>(queryPC[qp] = "exit")

====