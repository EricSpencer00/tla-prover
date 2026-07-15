---- MODULE Slush ----
EXTENDS Naturals, TLC

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
           SlushIterationCount, SampleSetSize, PickFlipThreshold,
           NoColor, NoMessage

(* --- Derived definitions --- *)

Color      == {"A", "B"}

HostL(lp)  == SELECT n : \E qp \in SlushQueryProcess : <lp, qp, n> \in HostMapping
HostQ(qp)  == SELECT n : \E lp \in SlushLoopProcess : <lp, qp, n> \in HostMapping

SampleSet(lp) == {qp \in SlushQueryProcess : HostQ(qp) # HostL(lp)}

MessageSet == {
    <<"query", lp, qp, c>> : lp \in SlushLoopProcess /\ qp \in SlushQueryProcess /\ c \in Color
  } \cup {
    <<"reply", qp, lp, c>> : qp \in SlushQueryProcess /\ lp \in SlushLoopProcess /\ c \in Color
  } \cup {
    <<"termination", lp>>   : lp \in SlushLoopProcess
  }

(* --- State variables --- *)

VARIABLES colors, msgs, sampleSets, iterCounts, termSent

(* --- Initial state --- *)

Init ==
    /\ colors \in [Node -> Color \cup {NoColor}]
       \* Every node starts uncolored
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ sampleSets \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ sampleSets = [lp \in SlushLoopProcess |-> {}]
    /\ iterCounts \in [SlushLoopProcess -> {0 .. SlushIterationCount}]
    /\ iterCounts = [lp \in SlushLoopProcess |-> 0]
    /\ termSent \in [SlushLoopProcess -> BOOLEAN]
    /\ termSent = [lp \in SlushLoopProcess |-> FALSE]

(* --- Actions --- *)

ClientAssign ==
    \E n \in Node :
        colors[n] = NoColor
        /\ UNCHANGED <<sampleSets, iterCounts, msgs, termSent>>
        /\ colors' = [colors EXCEPT ![n] = CHOOSE c \in Color |-> c]

LoopQuery(lp) ==
    \E lp \in SlushLoopProcess :
        /\ iterCounts[lp] < SlushIterationCount
        /\ termSent[lp] = FALSE
        /\ \E S \subseteq SampleSet(lp) : #S = SampleSetSize
        /\ UNCHANGED <<colors, msgs, termSent>>
        /\ sampleSets' = [sampleSets EXCEPT ![lp] = S]
        /\ msgs' = msgs \cup { <<"query", lp, qp, colors[HostL(lp)]>> : qp \in S }

RespondToQuery ==
    \E qp \in SlushQueryProcess :
        \E m \in msgs :
            /\ m[0] = "query"
            /\ m[2] = qp
            /\ UNCHANGED <<sampleSets, iterCounts, termSent>>
            /\ IF colors[HostQ(qp)] = NoColor THEN
                   colors' = [colors EXCEPT ![HostQ(qp)] = m[3]]
               ELSE
                   colors' = colors
            /\ msgs' = (msgs \ {m}) \cup { <<"reply", qp, m[1], colors[HostQ(qp)]>> }

TallyReplies(lp) ==
    \E lp \in SlushLoopProcess :
        /\ iterCounts[lp] < SlushIterationCount
        /\ sampleSets[lp] # {}
        /\ \A qp \in sampleSets[lp] : \E m \in msgs : m[0] = "reply" /\ m[1] = qp /\ m[2] = lp
        /\ UNCHANGED <<colors, sampleSets, iterCounts, termSent>>
        /\ LET replyColors == { m[3] : m \in msgs : m[0] = "reply" /\ m[2] = lp }
               countA == Cardinality({ c \in replyColors : c = "A" })
               countB == Cardinality({ c \in replyColors : c = "B" })
               newC   == IF countA >= PickFlipThreshold THEN "A"
                        ELSE IF countB >= PickFlipThreshold THEN "B"
                        ELSE colors[HostL(lp)]
           IN
           /\ colors' = [colors EXCEPT ![HostL(lp)] = newC]
           /\ sampleSets' = [sampleSets EXCEPT ![lp] = {}]
           /\ msgs' = msgs \ { m \in msgs : m[0] = "reply" /\ m[2] = lp }
           /\ iterCounts' = [iterCounts EXCEPT ![lp] = iterCounts[lp] + 1]

LoopSendTermination(lp) ==
    \E lp \in SlushLoopProcess :
        /\ iterCounts[lp] = SlushIterationCount
        /\ termSent[lp] = FALSE
        /\ UNCHANGED <<colors, sampleSets, iterCounts, msgs>>
        /\ msgs' = msgs \cup { <<"termination", lp>> }
        /\ termSent' = [termSent EXCEPT ![lp] = TRUE]

NoOp ==
    UNCHANGED <<colors, sampleSets, iterCounts, msgs, termSent>>

Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : LoopQuery(lp)
    \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
    \/ \E lp \in SlushLoopProcess : LoopSendTermination(lp)
    \/ RespondToQuery
    \/ NoOp

(* --- Specification --- *)

Spec == Init /\ [][Next]_<<colors, sampleSets, iterCounts, msgs, termSent>>

(* --- Type invariant --- *)

TypeInvariant ==
    /\ colors \in [Node -> Color \cup {NoColor}]
    /\ msgs \in MessageSet
    /\ sampleSets \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterCounts \in [SlushLoopProcess -> {0 .. SlushIterationCount}]
    /\ termSent \in [SlushLoopProcess -> BOOLEAN]

====