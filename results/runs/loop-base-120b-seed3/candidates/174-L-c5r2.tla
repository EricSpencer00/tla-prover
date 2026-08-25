---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants (to be supplied by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Node,                 \* Set of node identifiers
    SlushLoopProcess,     \* One loop process per node
    SlushQueryProcess,    \* One query process per node
    HostMapping,          \* Set of triples <<loopProc, queryProc, node>>
    SlushIterationCount,  \* Number of iterations each loop process performs
    SampleSetSize,        \* Size of the peer sample each iteration
    PickFlipThreshold,    \* Minimum count of a colour to cause a flip
    NoColor,              \* Symbol for “uncoloured’’
    NoMessage             \* Symbol for “no message’’ (placeholder)

(*-----------------------------------------------------------------
  Internal constants
-----------------------------------------------------------------*)
CONSTANTS Red, Blue          \* The two possible colours

ASSUME /\ Node # {}
       /\ SlushLoopProcess = Node
       /\ SlushQueryProcess = Node
       /\ Red # Blue
       /\ Red # NoColor /\ Blue # NoColor
       /\ \A n \in Node :
            \E lp \in SlushLoopProcess, qp \in SlushQueryProcess :
                <<lp, qp, n>> \in HostMapping

(*-----------------------------------------------------------------
  Derived mappings from HostMapping
-----------------------------------------------------------------*)
LoopNode == [lp \in SlushLoopProcess |-> 
               CHOOSE n \in Node : 
                 \E qp \in SlushQueryProcess : <<lp, qp, n>> \in HostMapping]

QueryNode == [qp \in SlushQueryProcess |-> 
                CHOOSE n \in Node : 
                  \E lp \in SlushLoopProcess : <<lp, qp, n>> \in HostMapping]

QueryOfNode == [n \in Node |-> 
                  CHOOSE qp \in SlushQueryProcess : 
                    \E lp \in SlushLoopProcess : <<lp, qp, n>> \in HostMapping]

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    color,          \* [Node -> (Red \/ Blue \/ {NoColor})]
    msgs,           \* Set of in‑flight messages
    sampleSet,      \* [SlushLoopProcess -> SUBSET SlushQueryProcess]
    iter,           \* [SlushLoopProcess -> Nat]  (how many iterations completed)
    pc               \* program counters for all processes

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
ColorSet == {Red, Blue}
Message == [type : {"query", "reply", "term"},
            src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            col  : ColorSet \cup {NoColor}]

PCValues == {"assign", "waitColor", "sample", "waitReplies",
             "terminate", "replyLoop", "done"}

(*-----------------------------------------------------------------
  Initialisation
-----------------------------------------------------------------*)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iter  = [lp \in SlushLoopProcess |-> 0]
    /\ pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 
                  IF p = "client" THEN "assign"
                  ELSE IF p \in SlushLoopProcess THEN "waitColor"
                  ELSE "replyLoop"]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
ClientAssign ==
    /\ pc["client"] = "assign"
    /\ \E n \in Node : color[n] = NoColor
    LET n  == CHOOSE m \in Node : color[m] = NoColor,
        col == CHOOSE c \in ColorSet : TRUE
    IN
       /\ color' = [color EXCEPT ![n] = col]
       /\ UNCHANGED <<msgs, sampleSet, iter, pc>>
       /\ pc' = [pc EXCEPT !["client"] = "assign"]

LoopRequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waitColor"
         /\ color[LoopNode[lp]] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "sample"]
         /\ UNCHANGED <<color, msgs, sampleSet, iter>>

LoopSample ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "sample"
         LET ownQ == QueryOfNode[LoopNode[lp]],
             cand  == SlushQueryProcess \ {ownQ},
             S     == CHOOSE s \in SUBSET cand :
                        Cardinality(s) = SampleSetSize
         IN
            /\ sampleSet' = [sampleSet EXCEPT ![lp] = S]
            /\ msgs' = msgs \cup 
                      { [type |-> "query",
                         src  |-> lp,
                         dst  |-> qp,
                         col  |-> color[LoopNode[lp]]] :
                        qp \in S }
            /\ pc' = [pc EXCEPT ![lp] = "waitReplies"]
            /\ UNCHANGED <<color, iter>>

QueryRespond ==
    /\ \E m \in msgs :
         /\ m.type = "query"
         LET qp == m.dst,
             n  == QueryNode[qp],
             newCol == IF color[n] = NoColor THEN m.col ELSE color[n],
             reply  == [type |-> "reply",
                        src  |-> qp,
                        dst  |-> m.src,
                        col  |-> newCol]
         IN
            /\ color' = [color EXCEPT ![n] = newCol]
            /\ msgs' = (msgs \ {m}) \cup {reply}
            /\ UNCHANGED <<sampleSet, iter, pc>>

LoopTally ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waitReplies"
         LET S       == sampleSet[lp],
             replies == { m \in msgs :
                           m.type = "reply" /\ m.dst = lp /\ m.src \in S }
         IN
            /\ Cardinality(replies) = SampleSetSize
            /\ reds  == Cardinality({ m \in replies : m.col = Red })
            /\ blues == Cardinality({ m \in replies : m.col = Blue })
            /\ newCol == IF reds >= PickFlipThreshold THEN Red
                        ELSE IF blues >= PickFlipThreshold THEN Blue
                        ELSE color[LoopNode[lp]]
            /\ color' = [color EXCEPT ![LoopNode[lp]] = newCol]
            /\ msgs' = msgs \ replies
            /\ iter' = [iter EXCEPT ![lp] = @ + 1]
            /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
            /\ pc' = IF iter'[lp] < SlushIterationCount
                     THEN [pc EXCEPT ![lp] = "sample"]
                     ELSE [pc EXCEPT ![lp] = "terminate"]
            /\ UNCHANGED <<>>

LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "terminate"
         /\ msgs' = msgs \cup 
                    { [type |-> "term",
                       src  |-> lp,
                       dst  |-> qp,
                       col  |-> NoColor] :
                      qp \in SlushQueryProcess }
         /\ pc' = [pc EXCEPT ![lp] = "done"]
         /\ UNCHANGED <<color, sampleSet, iter>>

QueryExit ==
    /\ \E qp \in SlushQueryProcess :
         /\ pc[qp] = "replyLoop"
         /\ \A lp \in SlushLoopProcess :
                \E m \in msgs :
                     /\ m.type = "term"
                     /\ m.src = lp
                     /\ m.dst = qp
         /\ pc' = [pc EXCEPT ![qp] = "done"]
         /\ UNCHANGED <<color, msgs, sampleSet, iter>>

Next ==
    \/ ClientAssign
    \/ LoopRequireColor
    \/ LoopSample
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryExit

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_(<<color, msgs, sampleSet, iter, pc>>)

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ color \in [Node -> (ColorSet \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> PCValues]

=============================================================================