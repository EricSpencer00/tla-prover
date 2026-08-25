---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Node,               \* Set of all node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Size of the peer sample taken each iteration
    PickFlipThreshold,  \* Minimum number of identical replies needed to flip color
    NoColor,            \* Special value meaning “uncolored”
    NoMessage           \* Special value used as a dummy message

\* ----------------------------------------------------------------------
\* Colors used by the protocol (two possible opinions)
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* Message definition (record)
\* ----------------------------------------------------------------------
Message == [type   : {"Query", "Reply", "Terminate"},
            src    : (SlushLoopProcess \cup SlushQueryProcess),
            dst    : (SlushLoopProcess \cup SlushQueryProcess),
            content: (Colors \cup {NoColor})]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,   \* mapping Node -> (Colors \cup {NoColor})
    msgs,    \* set of in‑flight Message records
    sample,  \* mapping SlushLoopProcess -> SUBSET SlushQueryProcess (current sample)
    iter     \* mapping SlushLoopProcess -> Nat (iterations completed)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Extract the node belonging to a given loop process
HostNode(p) == 
    CHOOSE t \in HostMapping : t[2] = p

\* Extract the query process belonging to a given node
QueryProc(n) == 
    CHOOSE t \in HostMapping : t[1] = n

\* Extract the loop process belonging to a given node
LoopProc(n) == 
    CHOOSE t \in HostMapping : t[1] = n

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Action: Client assigns a random color to an uncolored node
\* ----------------------------------------------------------------------
AssignColor ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ \E c \in Colors :
            /\ color' = [color EXCEPT ![n] = c]
            /\ UNCHANGED <<msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Action: Loop process waits until its host node is colored
\* ----------------------------------------------------------------------
RequireColor(p) ==
    LET n == HostNode(p) IN
    /\ color[n] # NoColor
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Action: Loop process selects a sample of peers (size = SampleSetSize)
\* ----------------------------------------------------------------------
SelectSample(p) ==
    LET qp == QueryProc(HostNode(p)) IN
    /\ sample' = [sample EXCEPT ![p] = 
            { q \in SlushQueryProcess \ {qp} :
                TRUE } 
          ]
    /\ Cardinality(sample'[p]) = SampleSetSize
    /\ UNCHANGED <<color, msgs, iter>>

\* ----------------------------------------------------------------------
\* Action: Loop process sends a Query message to each member of its sample
\* ----------------------------------------------------------------------
SendQueries(p) ==
    LET s == sample[p] IN
    /\ msgs' = msgs \cup 
        { [type |-> "Query",
           src  |-> p,
           dst  |-> q,
           content |-> 
               LET n == HostNode(p) IN color[n]] :
           q \in s }
    /\ UNCHANGED <<color, sample, iter>>

\* ----------------------------------------------------------------------
\* Action: Query process receives a Query, possibly adopts the color,
\*          and replies
\* ----------------------------------------------------------------------
RespondQuery(q) ==
    \E m \in msgs :
        /\ m.type = "Query"
        /\ m.dst = q
        LET n == HostNode(LoopProc(HostNode(q))) IN
        /\ IF color[n] = NoColor
           THEN color' = [color EXCEPT ![n] = m.content]
           ELSE UNCHANGED color
        /\ msgs' = (msgs \ {m}) \cup
            { [type    |-> "Reply",
               src     |-> q,
               dst     |-> m.src,
               content |-> 
                   LET n2 == HostNode(LoopProc(HostNode(q))) IN color[n2]] }
        /\ UNCHANGED <<sample, iter>>

\* ----------------------------------------------------------------------
\* Action: Loop process tallies replies, possibly flips its color,
\*          clears its sample, increments its iteration counter
\* ----------------------------------------------------------------------
TallyAndFlip(p) ==
    LET s == sample[p] IN
    LET replies == { m \in msgs :
                       /\ m.type = "Reply"
                       /\ m.dst = p
                       /\ m.src \in s } IN
    /\ Cardinality(replies) = SampleSetSize
    /\ LET redCnt == Cardinality({ r \in replies : r.content = "Red" }) IN
       blueCnt == Cardinality({ r \in replies : r.content = "Blue" }) IN
       \* decide whether to flip
       IF redCnt >= PickFlipThreshold
          THEN 
            LET n == HostNode(p) IN
            color' = [color EXCEPT ![n] = "Red"]
          ELSE IF blueCnt >= PickFlipThreshold
               THEN 
            LET n == HostNode(p) IN
            color' = [color EXCEPT ![n] = "Blue"]
               ELSE UNCHANGED color
    /\ msgs' = msgs \ { m \in replies : TRUE }   \* remove the processed replies
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iter' = [iter EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: Loop process terminates after completing all iterations
\* ----------------------------------------------------------------------
TerminateLoop(p) ==
    /\ iter[p] = SlushIterationCount
    /\ msgs' = msgs \cup { [type    |-> "Terminate",
                            src     |-> p,
                            dst     |-> NoMessage,
                            content |-> NoColor] }
    /\ UNCHANGED <<color, sample, iter>>

\* ----------------------------------------------------------------------
\* Action: Query processes exit when all termination messages have been seen
\* ----------------------------------------------------------------------
QueryExit(q) ==
    /\ \A p \in SlushLoopProcess :
          [type |-> "Terminate", src |-> p, dst |-> NoMessage, content |-> NoColor] \in msgs
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* The overall Next relation (any enabled action)
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in SlushLoopProcess : RequireColor(p)
    \/ \E p \in SlushLoopProcess : SelectSample(p)
    \/ \E p \in SlushLoopProcess : SendQueries(p)
    \/ \E q \in SlushQueryProcess : RespondQuery(q)
    \/ \E p \in SlushLoopProcess : TallyAndFlip(p)
    \/ \E p \in SlushLoopProcess : TerminateLoop(p)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ AssignColor

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant (safety property)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message

\* ----------------------------------------------------------------------
\* Liveness: all processes eventually terminate (expressed as a temporal
\* property that can be checked with TLC)
\* ----------------------------------------------------------------------
Termination ==
    \A p \in SlushLoopProcess : <> (iter[p] = SlushIterationCount)
    /\ \A q \in SlushQueryProcess : <> (UNCHANGED msgs)   \* placeholder

\* ----------------------------------------------------------------------
\* The set of invariants to be checked (as required by the .cfg file)
\* ----------------------------------------------------------------------
INVARIANT TypeInvariant

====