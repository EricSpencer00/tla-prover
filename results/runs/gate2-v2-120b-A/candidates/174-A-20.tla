---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples (<<proc, type, node>>)
    SlushIterationCount,\* Max number of iterations each loop performs
    SampleSetSize,      \* Number of peers sampled each round
    PickFlipThreshold,  \* Threshold of replies needed to flip color
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no message"

\* ----------------------------------------------------------------------
\* Derived mappings
\* ----------------------------------------------------------------------
\* From HostMapping we extract the node that a given process hosts.
HostOf(proc) == 
    IF proc \in SlushLoopProcess 
        THEN
            CHOOSE n \in Node : <<proc, "loop", n>> \in HostMapping
        ELSE IF proc \in SlushQueryProcess
            THEN
                CHOOSE n \in Node : <<proc, "query", n>> \in HostMapping
            ELSE NoColor

\* The set of all possible colors (two real colors plus NoColor)
Colors == {"Red", "Blue", NoColor}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,      \* [node -> Colors] current color of each node
    msgs,        \* Set of in‑flight messages
    pc,          \* [proc -> Nat] program counter of each process
    sample,      \* [loopProc -> SUBSET Node] peers sampled this round
    iter         \* [loopProc -> Nat] iterations completed so far

\* ----------------------------------------------------------------------
\* Message representation
\* ----------------------------------------------------------------------
\* A message is a record with a mandatory "type" field and other fields
\* depending on the type.
Msg == [type : {"query", "reply", "termination"},
        src  : (SlushLoopProcess \cup SlushQueryProcess),
        dst  : (SlushQueryProcess \cup SlushLoopProcess),
        clr  : Colors]  \* for query and reply; ignored for termination

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc     = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
UncoloredNodes == { n \in Node : colors[n] = NoColor }

\* Random selection is modeled nondeterministically.  The model
\* checker will explore all possibilities.
AssignRandomColor ==
    IF UncoloredNodes = {} THEN {} ELSE
        { <<n, c>> : n \in UncoloredNodes /\ c \in {"Red","Blue"} }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ pc["client"] = 0
    /\ \E assign \in AssignRandomColor :
        /\ colors' = [colors EXCEPT ![assign[1]] = assign[2]]
        /\ pc'     = [pc EXCEPT !["client"] = 1]
    /\ UNCHANGED <<msgs, sample, iter>>

RequireColor(lp) ==
    /\ pc[lp] = 0
    /\ colors[HostOf(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = 1]
    /\ UNCHANGED <<colors, msgs, sample, iter>>

SendQueries(lp) ==
    /\ pc[lp] = 1
    /\ LET peers == { HostOf(q) : q \in SlushQueryProcess \ { lp } } IN
       /\ sampleSet == { n \in peers : n \in Subset(pick = SampleSetSize, set = peers) }
    /\ sample' = [sample EXCEPT ![lp] = sampleSet]
    /\ msgs'   = msgs \cup
        { [type |-> "query",
           src  |-> lp,
           dst  |-> q,
           clr  |-> colors[HostOf(lp)] ] :
          q \in SlushQueryProcess /\ HostOf(q) \in sampleSet }
    /\ pc' = [pc EXCEPT ![lp] = 2]
    /\ UNCHANGED <<colors, iter>>

\* Query process handling a query
RespondQuery(qp) ==
    /\ pc[qp] = 0
    /\ \E m \in msgs :
        /\ m.type = "query"
        /\ m.dst = qp
        /\ LET node == HostOf(qp) IN
           /\ colors' = 
                IF colors[node] = NoColor
                    THEN [colors EXCEPT ![node] = m.clr]
                    ELSE colors
           /\ msgs' = (msgs \ {m}) \cup 
                { [type |-> "reply",
                   src  |-> qp,
                   dst  |-> m.src,
                   clr  |-> colors'[node] ] }
    /\ pc' = [pc EXCEPT ![qp] = 0]  \* stay in same state
    /\ UNCHANGED <<sample, iter>>

\* Loop process collecting a reply
CollectReply(lp) ==
    /\ pc[lp] = 2
    /\ \E r \in msgs :
        /\ r.type = "reply"
        /\ r.dst = lp
        /\ msgs' = msgs \ {r}
        /\ UNCHANGED <<colors, sample, iter, pc>>
    /\ UNCHANGED <<colors, msgs, sample, iter, pc>>

\* After all expected replies have been received, decide on flip
DecideFlip(lp) ==
    /\ pc[lp] = 2
    /\ \A n \in sample[lp] : 
        \E r \in msgs :
            r.type = "reply" /\ r.dst = lp /\ HostOf(r.src) = n
    /\ LET redCount == Cardinality(
            { n \in sample[lp] :
                \E r \in msgs :
                    r.type = "reply" /\ r.dst = lp /\ HostOf(r.src) = n /\ r.clr = "Red" })
        blueCount == Cardinality(
            { n \in sample[lp] :
                \E r \in msgs :
                    r.type = "reply" /\ r.dst = lp /\ HostOf(r.src) = n /\ r.clr = "Blue" })
        newClr == 
            IF redCount >= PickFlipThreshold THEN "Red"
            ELSE IF blueCount >= PickFlipThreshold THEN "Blue"
            ELSE colors[HostOf(lp)]
    /\ colors' = [colors EXCEPT ![HostOf(lp)] = newClr]
    /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
    /\ pc'     = [pc EXCEPT ![lp] = 
            IF @ + 1 >= SlushIterationCount THEN 3 ELSE 1]
    /\ UNCHANGED msgs

SendTermination(lp) ==
    /\ pc[lp] = 3
    /\ msgs' = msgs \cup 
        { [type |-> "termination",
           src  |-> lp,
           dst  |-> "client",
           clr  |-> NoColor] }
    /\ pc' = [pc EXCEPT ![lp] = 4]
    /\ UNCHANGED <<colors, sample, iter>>

TerminateClient ==
    /\ pc["client"] = 1
    /\ \A lp \in SlushLoopProcess :
        \E t \in msgs :
            t.type = "termination" /\ t.dst = "client"
    /\ msgs' = {}   \* clear termination messages
    /\ pc'   = [pc EXCEPT !["client"] = 2]
    /\ UNCHANGED <<colors, sample, iter>>

\* ----------------------------------------------------------------------
\* Stuttering step to avoid deadlock when everything is done
\* ----------------------------------------------------------------------
Done ==
    /\ pc["client"] = 2
    /\ \A p \in (SlushLoopProcess \cup SlushQueryProcess) : pc[p] = 4
    /\ UNCHANGED <<colors, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : SendQueries(lp)
    \/ \E qp \in SlushQueryProcess : RespondQuery(qp)
    \/ \E lp \in SlushLoopProcess : CollectReply(lp)
    \/ \E lp \in SlushLoopProcess : DecideFlip(lp)
    \/ \E lp \in SlushLoopProcess : SendTermination(lp)
    \/ TerminateClient
    \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> Colors]
    /\ msgs \subseteq { m \in [type : {"query","reply","termination"},
                               src  : (SlushLoopProcess \cup SlushQueryProcess),
                               dst  : (SlushQueryProcess \cup SlushLoopProcess \cup {"client"}),
                               clr  : Colors] :
                        (m.type = "query" => 
                            /\ m.src \in SlushLoopProcess
                            /\ m.dst \in SlushQueryProcess
                            /\ m.clr \in {"Red","Blue"})
                        /\ (m.type = "reply" => 
                            /\ m.src \in SlushQueryProcess
                            /\ m.dst \in SlushLoopProcess
                            /\ m.clr \in {"Red","Blue","NoColor"})
                        /\ (m.type = "termination" => 
                            /\ m.src \in SlushLoopProcess
                            /\ m.dst = "client"
                            /\ m.clr = NoColor) }
    /\ pc \in [ ("client") \cup SlushLoopProcess \cup SlushQueryProcess -> Nat]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ \A lp \in SlushLoopProcess : iter[lp] <= SlushIterationCount

\* ----------------------------------------------------------------------
\* The module's exported name
\* ----------------------------------------------------------------------
====