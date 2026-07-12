---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

\* -------------------------------------------------------------
\* Derived constants
\* -------------------------------------------------------------
Nodes           == Node
LoopPids        == SlushLoopProcess
QueryPids       == SlushQueryProcess
Colors          == {"RED", "BLUE"} \ {NoColor}
MsgTypes        == {"QUERY", "QUERY_REPLY", "TERMINATION"}
MessageSet      == [m \in SlushMsgTypes |-> {"From", "To", "Color"}]

\* -------------------------------------------------------------
\* State variables
\* -------------------------------------------------------------
VARIABLES
    Color,            \* [n \in Nodes |-> Colors \cup {NoColor}]
    Msg,              \* set of messages, each message is a record
    PC,               \* [p \in LoopPids \cup QueryPids |-> PCVal]
    Sample,           \* [p \in LoopPids |-> SUBSET QueryPids]
    Iter,             \* [p \in LoopPids |-> 0 .. SlushIterationCount]

\* -------------------------------------------------------------
\* Initialization
\* -------------------------------------------------------------
Init ==
    /\ Color = [n \in Nodes |-> NoColor]
    /\ Msg = {}
    /\ PC = [p \in LoopPids \cup QueryPids |
              IF p \in LoopPids THEN "waitColor"
              ELSE "reply"]
    /\ Sample = [p \in LoopPids |-> {}]
    /\ Iter   = [p \in LoopPids |-> 0]

\* -------------------------------------------------------------
\* Helper definitions
\* -------------------------------------------------------------
\* The set of all loop processes that have finished all iterations
FinishedLoops ==
    {p \in LoopPids : Iter[p] = SlushIterationCount}

\* The set of all query processes that have received all termination messages
FinishedQueries ==
    {q \in QueryPids :
        \A l \in LoopPids : "TERMINATION" \in Msg
            /\ Msg[["From"] = l /\ Msg[["To"]] = q /\ Msg[["Type"]] = "TERMINATION"]}

\* -------------------------------------------------------------
\* Client assigns color to an uncolored node
\* -------------------------------------------------------------
ClientAssign ==
    \E n \in Nodes :
        /\ Color[n] = NoColor
        /\ Color' = [Color EXCEPT ![n] = ChosenColor]
        /\ UNCHANGED PC, Msg, Sample, Iter
    \* ChosenColor is nondeterministically either RED or BLUE
    \E ChosenColor \in Colors

\* -------------------------------------------------------------
\* Loop process requires host color before starting iterations
\* -------------------------------------------------------------
RequireColor ==
    \E p \in LoopPids :
        /\ PC[p] = "waitColor"
        /\ Color[HostMapping[p]["Node"]] # NoColor
        /\ PC' = [PC EXCEPT ![p] = "query"]
        /\ UNCHANGED Color, Msg, Sample, Iter

\* -------------------------------------------------------------
\* Loop process queries a random sample of peers
\* -------------------------------------------------------------
QuerySampleSet ==
    \E p \in LoopPids :
        /\ PC[p] = "query"
        /\ \E S \in Subsets(QueryPids, SampleSetSize) :
              /\ S \ {p} = S   \* exclude own query process
              /\ Sample' = [Sample EXCEPT ![p] = S]
              /\ \E msg \in (\{\} \cup
                    [From |-> p,
                     To   |-> q,
                     Type |-> "QUERY",
                     Color |-> Color[HostMapping[p]["Node"]]
                     : q \in S]):
                    Msg' = Msg \cup {msg}
              /\ PC' = [PC EXCEPT ![p] = "waitReplies"]
              /\ UNCHANGED Color, Iter

\* -------------------------------------------------------------
\* Query process responds to a query
\* -------------------------------------------------------------
RespondToQuery ==
    \E q \in QueryPids :
        /\ PC[q] = "reply"
        /\ \E m \in Msg :
              /\ m.Type = "QUERY"
              /\ m.To = q
              /\ \E replyColor \in Colors :
                    /\ replyColor = IF Color[HostMapping[q]["Node"]] = NoColor
                                    THEN m.Color
                                    ELSE Color[HostMapping[q]["Node"]]
                    /\ Color' = [Color EXCEPT ![HostMapping[q]["Node"]] = replyColor]
                    /\ Msg' = Msg \ {m} \cup {[From |-> m.From,
                                                To   |-> q,
                                                Type |-> "QUERY_REPLY",
                                                Color |-> replyColor]}
                    /\ UNCHANGED PC, Sample, Iter

\* -------------------------------------------------------------
\* Loop process tallies replies and may flip color
\* -------------------------------------------------------------
TallyReplies ==
    \E p \in LoopPids :
        /\ PC[p] = "waitReplies"
        /\ \E replies \in {m \in Msg : m.Type = "QUERY_REPLY" /\ m.To = p} :
                /\ |replies| = Sample[p]    \* received all expected replies
                /\ CountRed   = Cardinality({m \in replies : m.Color = "RED"})
                /\ CountBlue  = Cardinality({m \in replies : m.Color = "BLUE"})
                /\ NewColor = IF CountRed >= PickFlipThreshold THEN "RED"
                              ELSE IF CountBlue >= PickFlipThreshold THEN "BLUE"
                              ELSE Color[HostMapping[p]["Node"]]
                /\ Color' = [Color EXCEPT ![HostMapping[p]["Node"]] = NewColor]
                /\ Sample' = [Sample EXCEPT ![p] = {}]
                /\ PC' = [PC EXCEPT ![p] = "checkDone"]
                /\ UNCHANGED Msg, Iter

\* -------------------------------------------------------------
\* Loop process checks if it should terminate
\* -------------------------------------------------------------
CheckDone ==
    \E p \in LoopPids :
        /\ PC[p] = "checkDone"
        /\ IF Iter[p] + 1 = SlushIterationCount THEN
              /\ Iter' = [Iter EXCEPT ![p] = Iter[p] + 1]
              /\ Msg' = Msg \cup {[From |-> p,
                                   To   |-> q,
                                   Type |-> "TERMINATION",
                                   Color |-> NoColor]
                                   : q \in QueryPids}
              /\ PC' = [PC EXCEPT ![p] = "done"]
              /\ UNCHANGED Color, Sample
           ELSE
              /\ Iter' = [Iter EXCEPT ![p] = Iter[p] + 1]
              /\ PC' = [PC EXCEPT ![p] = "query"]
              /\ UNCHANGED Color, Msg, Sample

\* -------------------------------------------------------------
\* Query processes exit after receiving all termination messages
\* -------------------------------------------------------------
ExitQuery ==
    \E q \in QueryPids :
        /\ PC[q] = "reply"
        /\ \A p \in LoopPids :
              "TERMINATION" \in Msg
              /\ Msg[["From"]] = p
              /\ Msg[["To"]] = q
              /\ Msg[["Type"]] = "TERMINATION"
        /\ PC' = [PC EXCEPT ![q] = "done"]
        /\ UNCHANGED Color, Msg, Sample, Iter

\* -------------------------------------------------------------
\* Next-state relation
\* -------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ RequireColor
    \/ QuerySampleSet
    \/ RespondToQuery
    \/ TallyReplies
    \/ CheckDone
    \/ ExitQuery

\* -------------------------------------------------------------
\* Specification
\* -------------------------------------------------------------
Spec == Init /\ [][Next]_<<Color, Msg, PC, Sample, Iter>>

\* -------------------------------------------------------------
\* Type invariant (safety property)
\* -------------------------------------------------------------
TypeInvariant ==
    /\ Color \in [Nodes |-> Colors \cup {NoColor}]
    /\ Msg \subseteq { [From |-> p, To |-> q,
                        Type |-> t, Color |-> c]
                      : p \in LoopPids \cup QueryPids,
                        q \in LoopPids \cup QueryPids,
                        t \in MsgTypes,
                        IF t = "QUERY" \/ t = "QUERY_REPLY" THEN c \in Colors ELSE c = NoColor }
    /\ PC \in [LoopPids \cup QueryPids |-> {"waitColor", "query", "waitReplies",
                                            "checkDone", "reply", "done"}]
    /\ Sample \in [LoopPids |-> SUBSET QueryPids]
    /\ Iter \in [LoopPids |-> 0 .. SlushIterationCount]

====