---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

ASSUME NoColor \notin Node \and NoMessage \notin Node

VARIABLES assignment, inbox, pcLoop, pcQuery, querySet, iteration

vars == <<assignment, inbox, pcLoop, pcQuery, querySet, iteration>>

Link(p) == CHOOSE t \in HostMapping : t[1] = p
NodeOf(t) == t[2]

ColorView(n) == assignment[n] \in {0, 1}

Responses(p) == {m \in inbox : m[1] = p}
ClearResponses(p) == {m \in inbox : m[1] # p}
ReceivedCount(p, c) == Cardinality({m \in Responses(p) : m[3] = c})

Init ==
    /\ assignment = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ pcLoop = [p \in SlushLoopProcess |-> "waiting"]
    /\ pcQuery = [q \in SlushQueryProcess |-> "replying"]
    /\ querySet = [p \in SlushLoopProcess |-> {}]
    /\ iteration = [p \in SlushLoopProcess |-> 0]

AssignColor ==
    /\ \E n \in Node, c \in {0, 1} :
         /\ assignment[n] = NoColor
         /\ assignment' = [assignment EXCEPT ![n] = c]
    /\ UNCHANGED <<inbox, pcLoop, pcQuery, querySet, iteration>>

RequireColor ==
    /\ \E p \in SlushLoopProcess :
         /\ pcLoop[p] = "waiting"
         /\ assignment[NodeOf(Link(p))] \in {0, 1}
         /\ pcLoop' = [pcLoop EXCEPT ![p] = "querying"]
    /\ UNCHANGED <<assignment, inbox, pcQuery, querySet, iteration>>

QuerySampleSet ==
    /\ \E p \in SlushLoopProcess :
         /\ pcLoop[p] = "querying"
         /\ \E Q \in SUBSET SlushQueryProcess :
              /\ Q # {}
              /\ Cardinality(Q) <= SampleSetSize
              /\ querySet' = [querySet EXCEPT ![p] = Q]
              /\ inbox' = inbox \union {[q, p, assignment[NodeOf(Link(p))]] : q \in Q}
         /\ pcLoop' = [pcLoop EXCEPT ![p] = "tallying"]
    /\ UNCHANGED <<assignment, pcQuery, iteration>>

RespondToQuery ==
    /\ \E m \in inbox :
         /\ m[1] \in SlushQueryProcess
         /\ LET t == Link(m[1]) IN
              /\ assignment[NodeOf(t)] = NoColor
                 => assignment' = [assignment EXCEPT ![NodeOf(t)] = m[3]]
              /\ inbox' = (inbox \ {m}) \union {[m[1], m[2], assignment[NodeOf(t)]]}
         /\ UNCHANGED <<pcLoop, pcQuery, querySet, iteration>>

TallyReplies ==
    /\ \E p \in SlushLoopProcess :
         /\ pcLoop[p] = "tallying"
         /\ Cardinality(Responses(p)) = Cardinality(querySet[p])
         /\ \E c \in {0, 1} :
              /\ ReceivedCount(p, c) >= PickFlipThreshold
              /\ assignment' = [assignment EXCEPT ![NodeOf(Link(p))] = c]
         /\ pcLoop' = [pcLoop EXCEPT ![p] = "doneLoop"]
         /\ querySet' = [querySet EXCEPT ![p] = {}]
         /\ inbox' = ClearResponses(p)
         /\ iteration' = [iteration EXCEPT ![p] = @ + 1]
    /\ UNCHANGED pcQuery

LoopTerminate ==
    /\ \E p \in SlushLoopProcess :
         /\ pcLoop[p] = "doneLoop"
         /\ iteration[p] = SlushIterationCount
         /\ pcLoop' = [pcLoop EXCEPT ![p] = "done"]
         /\ inbox' = inbox \union {[p, NoMessage, NoMessage]}
    /\ UNCHANGED <<assignment, pcQuery, querySet, iteration>>

QueryLoopExit ==
    /\ \E q \in SlushQueryProcess :
         /\ pcQuery[q] = "replying"
         /\ \A p \in SlushLoopProcess : [p, NoMessage, NoMessage] \in inbox
         /\ pcQuery' = [pcQuery EXCEPT ![q] = "done"]
    /\ UNCHANGED <<assignment, inbox, pcLoop, querySet, iteration>>

Next ==
    \/ AssignColor \/ RequireColor \/ QuerySampleSet
    \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(AssignColor) /\ WF_vars(RequireColor)
    /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
    /\ WF_vars(TallyReplies) /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

TypeInvariant ==
    /\ assignment \in [Node -> Node \union {NoColor}]
    /\ inbox \subseteq (SlushQueryProcess \union SlushLoopProcess) \X Node \union (Node \union {NoColor})

Termination ==
    /\ \A p \in SlushLoopProcess : pcLoop[p] = "done"
    /\ \A q \in SlushQueryProcess : pcQuery[q] = "done"

====