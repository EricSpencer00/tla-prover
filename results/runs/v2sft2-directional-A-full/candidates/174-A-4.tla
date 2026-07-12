---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"} \cup {NoColor}
Process == SlushLoopProcess \cup SlushQueryProcess
Message == {"Query", "QueryReply", "Terminate",
            "ClientAssign"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    colors,          \* [node -> color]
    msgSet,          \* SUBSET of MessageSet
    pc,              \* [process -> {"AwaitColor","QuerySampleSet", 
                                 "WaitReplies","TallyReply","EndLoop",
                                 "ReplyLoop","Exit" }]
    sampleSets,      \* [loopProcess -> SUBSET SlushQueryProcess]
    iterCounts       \* [loopProcess -> 0..SlushIterationCount]
    terminated       \* SUBSET SlushLoopProcess
    assignedNodes    \* SUBSET Node  \* nodes that have received a color

\* ----------------------------------------------------------------------
\* Helpers
\* ----------------------------------------------------------------------
QueryMsg(lp, qp, color) ==
    << "Query", lp, qp, color >>

QueryReplyMsg(qp, lp, color) ==
    << "QueryReply", qp, lp, color >>

TerminateMsg(lp) ==
    << "Terminate", lp >>

ClientAssignMsg(node, color) ==
    << "ClientAssign", node, color >>

HostOf[lp] ==
    LET pair \in HostMapping : pair[1] = lp IN
    pair[2]              \* returns the node belonging to loop process lp

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgSet = {}
    /\ pc = [p \in Process |-> IF p \in SlushLoopProcess
                THEN "AwaitColor"
                ELSE "ReplyLoop"]
    /\ sampleSets = [lp \in SlushLoopProcess |-> {}]
    /\ iterCounts = [lp \in SlushLoopProcess |-> 0]
    /\ terminated = {}
    /\ assignedNodes = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    \E n \in Node \ {n \in assignedNodes} :
        /\ colors' = [colors EXCEPT ![n] = CHOOSE c \in Color : c # NoColor]
        /\ assignedNodes' = assignedNodes \cup {n}
        /\ UNCHANGED << msgSet, pc, sampleSets, iterCounts, terminated >>

RequireColor(lp) ==
    /\ pc[lp] = "AwaitColor"
    /\ colors[HostOf[lp]] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "QuerySampleSet"]
    /\ UNCHANGED << colors, msgSet, sampleSets, iterCounts, terminated, assignedNodes >>

QuerySampleSet(lp) ==
    /\ pc[lp] = "QuerySampleSet"
    /\ \E sample \in Subsets(SlushQueryProcess, SampleSetSize) :
        /\ sampleSets' = [sampleSets EXCEPT ![lp] = sample]
        /\ \E qp \in sample :
            /\ msgSet' = msgSet \cup { QueryMsg(lp, qp, colors[HostOf[lp]]) }
        /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
        /\ UNCHANGED << colors, iterCounts, terminated, assignedNodes >>

HandleQuery(qp) ==
    /\ \E msg \in msgSet : msg[1] = "Query"
    /\ \E msg \in msgSet : msg[3] = qp
    /\ \E lp \in SlushLoopProcess :
           /\ msg[2] = lp
           /\ msg[4] = color
    /\ IF colors[HostOf[qp]] = NoColor
          THEN colors' = [colors EXCEPT ![HostOf[qp]] = msg[4]]
          ELSE UNCHANGED colors
    /\ msgSet' = msgSet \ {msg}
    /\ msgSet' = msgSet' \cup { QueryReplyMsg(qp, msg[2], colors[HostOf[qp]]) }
    /\ UNCHANGED << pc, sampleSets, iterCounts, terminated, assignedNodes >>

WaitReplies(lp) ==
    /\ pc[lp] = "WaitReplies"
    /\ \A qp \in sampleSets[lp] : 
           \E msg \in msgSet : msg[1] = "QueryReply" /\ msg[2] = qp /\ msg[4] \in { "Red", "Blue" }
    /\ pc' = [pc EXCEPT ![lp] = "TallyReply"]
    /\ UNCHANGED << colors, msgSet, sampleSets, iterCounts, terminated, assignedNodes >>

TallyReply(lp) ==
    /\ pc[lp] = "TallyReply"
    /\ let replies == { msg[4] : msg \in msgSet : msg[1] = "QueryReply" /\ msg[2] \in sampleSets[lp] } in
       /\ \E colorVal \in {"Red", "Blue"} :
              Cardinality({ m \in replies : m = colorVal }) >= PickFlipThreshold
           => colors' = [colors EXCEPT ![HostOf[lp]] = colorVal]
       /\ UNCHANGED colors
    /\ sampleSets' = [sampleSets EXCEPT ![lp] = {}]
    /\ UNCHANGED iterCounts
    /\ pc' = [pc EXCEPT ![lp] = "EndLoop"]
    /\ UNCHANGED msgSet

EndLoop(lp) ==
    /\ pc[lp] = "EndLoop"
    /\ iterCounts[lp] < SlushIterationCount
    /\ iterCounts' = [iterCounts EXCEPT ![lp] = iterCounts[lp] + 1]
    /\ msgSet' = msgSet \cup { TerminateMsg(lp) }
    /\ pc' = [pc EXCEPT ![lp] = "QuerySampleSet"]
    /\ UNCHANGED << colors, sampleSets, terminated, assignedNodes >>

TerminateAll(lp) ==
    /\ pc[lp] = "EndLoop"
    /\ iterCounts[lp] = SlushIterationCount
    /\ terminated' = terminated \cup {lp}
    /\ UNCHANGED << colors, pc, sampleSets, iterCounts, msgSet, assignedNodes >>

ReplyLoop(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E msg \in msgSet : msg[1] = "Query" /\ msg[2] \in SlushLoopProcess /\ msg[3] = qp
    /\ HandleQuery(qp)
    /\ UNCHANGED << pc, sampleSets, iterCounts, terminated, assignedNodes >>

ReplyExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ terminated = SlushLoopProcess
    /\ pc' = [pc EXCEPT ![qp] = "Exit"]
    /\ UNCHANGED << colors, msgSet, sampleSets, iterCounts, terminated, assignedNodes >>

Next ==
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : QuerySampleSet(lp)
    \/ \E qp \in SlushQueryProcess : ReplyLoop(qp)
    \/ \E lp \in SlushLoopProcess : WaitReplies(lp)
    \/ \E lp \in SlushLoopProcess : TallyReply(lp)
    \/ \E lp \in SlushLoopProcess : EndLoop(lp)
    \/ \E lp \in SlushLoopProcess : TerminateAll(lp)
    \/ \E qp \in SlushQueryProcess : ReplyExit(qp)
    \/ \E n \in Node : ClientAssign

Spec == Init /\ [][Next]_<<colors, msgSet, pc, sampleSets, iterCounts, terminated, assignedNodes>>

\* ----------------------------------------------------------------------
\* Type invariant (the only one required)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> Color]
    /\ msgSet \subseteq { << "Query", lp, qp, color >> :
                      lp \in SlushLoopProcess /\ qp \in SlushQueryProcess /\ color \in Color } \cup
                 { << "QueryReply", qp, lp, color >> :
                      qp \in SlushQueryProcess /\ lp \in SlushLoopProcess /\ color \in Color } \cup
                 { << "Terminate", lp >> : lp \in SlushLoopProcess } \cup
                 { << "ClientAssign", n, color >> :
                      n \in Node /\ color \in Color \ { NoColor } }
    /\ pc \in [Process -> {"AwaitColor","QuerySampleSet","WaitReplies",
                           "TallyReply","EndLoop","ReplyLoop","Exit"}]
    /\ sampleSets \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterCounts \in [SlushLoopProcess -> 0..SlushIterationCount]
    /\ terminated \subseteq SlushLoopProcess
    /\ assignedNodes \subseteq Node

====