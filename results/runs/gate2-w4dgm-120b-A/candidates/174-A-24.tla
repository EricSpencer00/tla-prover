---- MODULE Slush ----
EXTENDS Naturals

(* Slush is the simplest member of the Snow family of probabilistic           *)
(* consensus protocols.  Nodes run a loop: they sample a random set of peers,   *)
(* collect replies, and adopt a color if enough peers reported it.  Because TLC   *)
(* has no probabilistic choice, this serves as executable pseudocode for the      *)
(* protocol rather than a statistical proof of convergence.                       *)

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess,
    HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

\* A loop process drives a node's Slush iteration; a query process replies to  *
\* polls from its peers.  HostMapping links each node to its loop and query    *
\* processes in both directions.                                              *
Process == SlushLoopProcess \cup SlushQueryProcess
Uncolored == [n \in Node |-> NoColor]

MessageDomain ==
    UNION {[src: SlushQueryProcess, dst: SlushLoopProcess,
             kind: "query", which: 1..2, nd: Node] :
            \E nd \in Node : TRUE}
        \cup
    {[src: SlushQueryProcess, dst: SlushLoopProcess,
             kind: "reply", which: 1..2, nd: Node] : \E nd \in Node : TRUE}
        \cup
    {[src: SlushLoopProcess, dst: SlushLoopProcess, kind: "done"} : TRUE

VARIABLES color, messages, pc, sampleSet, iteration

vars == <<color, messages, pc, sampleSet, iteration>>

TypeOK ==
    /\ color \in [Node -> {NoColor, 1, 2}]
    /\ messages \subseteq MessageDomain
    /\ pc \in [Process -> {"init", "require", "query", "tally", "loop", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = Uncolored
    /\ messages = {}
    /\ pc = [p \in Process |-> IF p \in SlushLoopProcess THEN "require" ELSE "loop"]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ iteration = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node; this seeds the   *
\* Slush process and models an external transaction arriving at the network.   *
ClientAssignsColor ==
    \E n \in Node, c \in {1, 2} :
        /\ color[n] = NoColor
        /\ color' = [color EXCEPT ![n] = c]
        /\ UNCHANGED <<messages, pc, sampleSet, iteration>>

RequireColor ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "require"
        /\ (\E e \in HostMapping : e.lp = lp /\ color[e.nd] # NoColor)
        /\ pc' = [pc EXCEPT ![lp] = "query"]
        /\ UNCHANGED <<color, messages, sampleSet, iteration>>

QuerySampleSet ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "query"
        /\ iteration[lp] < SlushIterationCount
        /\ \E ss \in SUBSET SlushQueryProcess :
             /\ Cardinality(ss) = SampleSetSize
             /\ sampleSet' = [sampleSet EXCEPT ![lp] = ss]
             /\ messages' = messages \cup
                 {[src |-> qp, dst |-> lp, kind |-> "query", which |-> 2,
                    nd |-> (CHOOSE e \in HostMapping : e.qp = qp).nd]
                  : qp \in ss}
        /\ pc' = [pc EXCEPT ![lp] = "tally"]
        /\ UNCHANGED <<color, iteration>>

RespondToQuery ==
    \E m \in messages :
        /\ m.kind = "query"
        /\ messages' = messages \ {m} \cup
            {[src |-> m.src, dst |-> m.dst, kind |-> "reply", which |-> 1, nd |-> m.nd]}
        /\ color' = IF color[m.nd] = NoColor
                    THEN [color EXCEPT ![m.nd] = m.which]
                    ELSE color
        /\ UNCHANGED <<pc, sampleSet, iteration>>

TallyReplies ==
    \* When all sampled peers have replied, adopt a color that meets the       *
    \* flip threshold; otherwise just advance the iteration.                  *
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "tally"
        /\ \A qp \in sampleSet[lp] :
            \E m \in messages : m.src = qp /\ m.dst = lp /\ m.kind = "reply"
        /\ LET tally(c) ==
                Cardinality({qp \in sampleSet[lp] :
                    (CHOOSE m \in messages : m.src = qp /\ m.dst = lp /\ m.kind = "reply").which = c})
           IN
            color' = IF \E c \in {1, 2} : tally(c) >= PickFlipThreshold
                     THEN [color EXCEPT ![(CHOOSE e \in HostMapping : e.lp = lp).nd] = CHOOSE c \in {1, 2} : tally(c) >= PickFlipThreshold]
                     ELSE color
        /\ pc' = [pc EXCEPT ![lp] = "loop"]
        /\ iteration' = [iteration EXCEPT ![lp] = iteration[lp] + 1]
        /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
        /\ UNCHANGED messages

LoopTermination ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "loop"
        /\ iteration[lp] >= SlushIterationCount
        /\ pc' = [pc EXCEPT ![lp] = "done"]
        /\ messages' = messages \cup
            {[src |-> lp, dst |-> lp, kind |-> "done"}]
        /\ UNCHANGED <<color, sampleSet, iteration>>

QueryLoopExit ==
    /\ \A qp \in SlushQueryProcess : pc[qp] = "loop"
    /\ \A lp \in SlushLoopProcess : [src |-> lp, dst |-> lp, kind |-> "done"] \in messages
    /\ pc' = [p \in Process |-> IF p \in SlushQueryProcess THEN "done" ELSE pc[p]]
    /\ UNCHANGED <<color, messages, sampleSet, iteration>>

Next ==
    \/ ClientAssignsColor \/ RequireColor \/ QuerySampleSet
    \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignsColor) /\ WF_vars(RequireColor)
            /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
            /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)
            /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

AllProcessesEventuallyDone == <>(\A p \in Process : pc[p] = "done")

====