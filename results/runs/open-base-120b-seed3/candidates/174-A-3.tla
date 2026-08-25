---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS 
    Node,                 \* Set of all node identifiers
    SlushLoopProcess,     \* Set of loop process identifiers (one per node)
    SlushQueryProcess,    \* Set of query process identifiers (one per node)
    HostMapping,          \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,  \* Number of iterations each loop process performs
    SampleSetSize,        \* Size of the random sample each loop process draws
    PickFlipThreshold,    \* Threshold for flipping to a color
    NoColor,              \* Special value meaning “uncolored”
    NoMessage             \* Special value used in termination messages

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

MessageType == {"query", "reply", "term"}

Message ==
    { [type  |-> t,
       src   |-> s,
       dst   |-> d,
       color |-> c] :
        t \in MessageType                 /\
        s \in (SlushLoopProcess \cup SlushQueryProcess) /\
        d \in (SlushLoopProcess \cup SlushQueryProcess \cup {"all"}) /\
        c \in (Colors \cup {NoColor, NoMessage}) }

LoopHost(lp) ==
    CHOOSE n \in Node : <<n, lp, _>> \in HostMapping

QueryHost(qp) ==
    CHOOSE n \in Node : <<n, _, qp>> \in HostMapping

OtherNodes(lp) ==
    Node \ { LoopHost(lp) }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES colors, msgs, sampleSet, iter

\* colors : Node -> (Colors \cup {NoColor})
\* msgs   : set of Message
\* sampleSet : SlushLoopProcess -> SUBSET Node   (current sample)
\* iter   : SlushLoopProcess -> Nat               (iterations completed)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors    = [n \in Node |-> NoColor]
    /\ msgs      = {}
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iter      = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    \E n \in Node :
        /\ colors[n] = NoColor
        /\ \E c \in Colors :
               /\ colors' = [colors EXCEPT ![n] = c]
               /\ UNCHANGED <<msgs, sampleSet, iter>>

RequireColor(lp) ==
    /\ colors[LoopHost(lp)] # NoColor
    /\ UNCHANGED <<colors, msgs, sampleSet, iter>>

PickSample(lp) ==
    \E samp \subseteq OtherNodes(lp) :
        /\ Cardinality(samp) = SampleSetSize
        /\ sampleSet' = [sampleSet EXCEPT ![lp] = samp]
        /\ UNCHANGED <<colors, msgs, iter>>

SendQueries(lp) ==
    LET node   == LoopHost(lp)                IN
    LET samp   == sampleSet[lp]               IN
    LET targets == { qp \in SlushQueryProcess :
                       QueryHost(qp) \in samp } IN
    /\ msgs' = msgs \cup
               { [type  |-> "query",
                  src   |-> lp,
                  dst   |-> qp,
                  color |-> colors[node]] :
                     qp \in targets }
    /\ UNCHANGED <<colors, sampleSet, iter>>

ReceiveAllReplies(lp) ==
    LET samp   == sampleSet[lp]               IN
    LET targets == { qp \in SlushQueryProcess :
                       QueryHost(qp) \in samp } IN
    /\ \A qp \in targets :
          \E m \in msgs :
               /\ m.type = "reply"
               /\ m.src  = qp
               /\ m.dst  = lp
    /\ UNCHANGED <<colors, msgs, sampleSet, iter>>

TallyAndFlip(lp) ==
    LET node   == LoopHost(lp)                IN
    LET samp   == sampleSet[lp]               IN
    LET targets == { qp \in SlushQueryProcess :
                       QueryHost(qp) \in samp } IN
    LET reds ==
          Cardinality(
            { qp \in targets :
                \E m \in msgs :
                     /\ m.type = "reply"
                     /\ m.src  = qp
                     /\ m.dst  = lp
                     /\ m.color = "Red" })
    IN
    LET blues ==
          Cardinality(
            { qp \in targets :
                \E m \in msgs :
                     /\ m.type = "reply"
                     /\ m.src  = qp
                     /\ m.dst  = lp
                     /\ m.color = "Blue" })
    IN
    LET newColor ==
          IF reds >= PickFlipThreshold THEN "Red"
          ELSE IF blues >= PickFlipThreshold THEN "Blue"
          ELSE colors[node]
    IN
    /\ colors'    = [colors EXCEPT ![node] = newColor]
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ iter'      = [iter EXCEPT ![lp] = iter[lp] + 1]
    /\ UNCHANGED msgs

TerminateLoop(lp) ==
    /\ iter[lp] >= SlushIterationCount
    /\ msgs' = msgs \cup { [type |-> "term",
                           src  |-> lp,
                           dst  |-> "all",
                           color|-> NoMessage] }
    /\ UNCHANGED <<colors, sampleSet, iter>>

QueryRespond(qp) ==
    \E m \in msgs :
        /\ m.type = "query"
        /\ m.dst  = qp
    LET node == QueryHost(qp) IN
    LET adoptColor ==
          IF colors[node] = NoColor THEN m.color ELSE colors[node] IN
    /\ colors' = [colors EXCEPT ![node] = adoptColor]
    /\ msgs'   = msgs \cup
                { [type  |-> "reply",
                   src   |-> qp,
                   dst   |-> m.src,
                   color |-> adoptColor] }
    /\ UNCHANGED <<sampleSet, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : PickSample(lp)
    \/ \E lp \in SlushLoopProcess : SendQueries(lp)
    \/ \E lp \in SlushLoopProcess : ReceiveAllReplies(lp)
    \/ \E lp \in SlushLoopProcess : TallyAndFlip(lp)
    \/ \E lp \in SlushLoopProcess : TerminateLoop(lp)
    \/ \E qp \in SlushQueryProcess : QueryRespond(qp)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, sampleSet, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> (Colors \cup {NoColor})]
    /\ msgs   \subseteq Message

\* ----------------------------------------------------------------------
\* The declared invariant for the configuration
\* ----------------------------------------------------------------------
INVARIANT TypeInvariant

====