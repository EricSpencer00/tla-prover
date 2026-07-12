---- MODULE Slush ----
EXTENDS FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (declared in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
           SlushIterationCount, SampleSetSize, PickFlipThreshold,
           NoColor, NoMessage

\* ----------------------------------------------------------------------
\* Derived types
\* ----------------------------------------------------------------------
Colors == {"red", "blue"}
MsgType == {"query", "reply", "termin"}
AllProcs == SlushLoopProcess \cup SlushQueryProcess \cup {Client}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES colors, msgs, pc, sample, iter, terminatedLoops

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK ==
    /\ colors \in [n \in Node |-> Colors \cup {NoColor}]
    /\ msgs \in SUBSET { <<t, f, tgt, c>> |
                      t \in MsgType
                      /\ f \in SlushLoopProcess \cup SlushQueryProcess \cup {Client}
                      /\ (t = "termin" /\ tgt = "ALL" /\ c \in {NoColor})
                      \/ (t \in {"query", "reply"} /\ tgt \in SlushLoopProcess \cup SlushQueryProcess)
                      /\ c \in Colors \cup {NoColor} }
    /\ pc \in [p \in AllProcs |-> {"Init", "RequireColor", "QuerySampleSet",
                                   "WaitReplies", "Tally", "Terminate",
                                   "Done", "Waiting"}]
    /\ sample \in [lp \in SlushLoopProcess |-> SUBSET SlushQueryProcess]
    /\ iter \in [lp \in SlushLoopProcess |-> 0..SlushIterationCount]
    /\ terminatedLoops \subseteq SlushLoopProcess

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in AllProcs |-> "Init"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter = [lp \in SlushLoopProcess |-> 0]
    /\ terminatedLoops = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Client assigns a random color to an uncolored node
ClientAssign ==
    \E n \in Node : colors[n] = NoColor :
        /\ colors' = [colors EXCEPT ![n] = CHOOSE c \in Colors : TRUE]
        /\ pc'   = [pc EXCEPT ![Client] = "Waiting"]
        /\ UNCHANGED <<msgs, sample, iter, terminatedLoops>>

\* Client stays in waiting state after all nodes are colored
ClientDone ==
    /\ \A n \in Node : colors[n] \in Colors
    /\ pc[Client] = "Waiting"
    /\ pc' = [pc EXCEPT ![Client] = "Done"]
    /\ UNCHANGED <<colors, msgs, sample, iter, terminatedLoops>>

\* Loop process requires its node to be colored before proceeding
RequireColor ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "RequireColor"
        /\ colors[HostMapping[lp]] \in Colors
        /\ pc' = [pc EXCEPT ![lp] = "QuerySampleSet"]
        /\ UNCHANGED <<colors, msgs, sample, iter, terminatedLoops>>

\* Loop process selects a sample of query processes and sends query messages
QuerySampleSet ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "QuerySampleSet"
        /\ \E S \in {s \in SUBSET SlushQueryProcess : Cardinality(s) = SampleSetSize} :
            /\ sample' = [sample EXCEPT ![lp] = S]
            /\ msgs'   = msgs \cup { <<"query", lp, qp, colors[HostMapping[lp]]>> : qp \in S }
            /\ pc'     = [pc EXCEPT ![lp] = "WaitReplies"]
            /\ UNCHANGED <<colors, iter, terminatedLoops>>

\* Query process responds to a query message
RespondToQuery ==
    \E qp \in SlushQueryProcess :
        \E m \in msgs :
            /\ m = <<"query", lp, qp, colorFrom>> 
            /\ pc[qp] \in {"Init", "Waiting", "Done"} 
            /\ LET node == HostMapping[qp] IN
               /\ IF colors[node] = NoColor
                  THEN colors' = [colors EXCEPT ![node] = colorFrom]
                  ELSE colors' = colors
               /\ msgs' = msgs \ {m} \cup { <<"reply", qp, lp, colors[node]>> }
               /\ UNCHANGED <<pc, sample, iter, terminatedLoops>>

\* Loop process tallies replies and updates its node's color if threshold met
TallyReplies ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = "WaitReplies"
        /\ LET S == sample[lp] IN
           /\ \A qp \in S : <<"reply", qp, lp, _>> \in msgs
           /\ LET replyColors == { c : <<"reply", qp, lp, c>> \in msgs | qp \in S } IN
              /\ IF Cardinality({c \in replyColors : c = "red"}) >= PickFlipThreshold
                 THEN newColor == "red"
                 ELSE IF Cardinality({c \in replyColors : c = "blue"}) >= PickFlipThreshold
                        THEN newColor == "blue"
                        ELSE newColor == colors[HostMapping[lp]]
              /\ colors' = [colors EXCEPT ![HostMapping[lp]] = newColor]
              /\ sample' = [sample EXCEPT ![lp] = {}]
              /\ iter'   = [iter EXCEPT ![lp] = iter[lp] + 1]
              /\ msgs'   = msgs \ { <<"reply", qp, lp, _>> : qp \in S }
              /\ IF iter'[lp] < SlushIterationCount
                 THEN pc' = [pc EXCEPT ![lp] = "RequireColor"]
                 ELSE pc' = [pc EXCEPT ![lp] = "Terminate"]
              /\ IF iter'[lp] >= SlushIterationCount
                    THEN msgs' = msgs' \cup { <<"termin", lp, "ALL", NoColor>> }
              /\ UNCHANGED <<pc, terminatedLoops>>

\* Process a termination message
ProcessTermination ==
    \E m \in msgs :
        /\ m = <<"termin", lp, "ALL", NoColor>>
        /\ pc[lp] = "Terminate"
        /\ msgs' = msgs \ {m}
        /\ pc'   = [pc EXCEPT ![lp] = "Done"]
        /\ terminatedLoops' = terminatedLoops \cup {lp}
        /\ UNCHANGED <<colors, sample, iter>>

\* Query processes exit when all loop processes have terminated
QueryLoopExit ==
    \E qp \in SlushQueryProcess :
        /\ pc[qp] \in {"Init", "Waiting", "Done"}
        /\ terminatedLoops = SlushLoopProcess
        /\ pc' = [pc EXCEPT ![qp] = "Done"]
        /\ UNCHANGED <<colors, msgs, sample, iter, terminatedLoops>>

\* ----------------------------------------------------------------------
\* Next state relation (disjunction of all actions)
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ ClientDone
    \/ RequireColor
    \/ QuerySampleSet
    \/ RespondToQuery
    \/ TallyReplies
    \/ ProcessTermination
    \/ QueryLoopExit

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, pc, sample, iter, terminatedLoops>>

\* ----------------------------------------------------------------------
\* Type invariant (used by TLC)
\* ----------------------------------------------------------------------
TypeInvariant == TypeOK

====