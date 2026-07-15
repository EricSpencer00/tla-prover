---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants (to be supplied in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples [loop |-> p, query |-> q, node |-> n]
    SlushIterationCount,\* Number of iterations each loop process must run
    SampleSetSize,      \* Size of the random sample each loop process selects
    PickFlipThreshold,  \* Threshold of matching replies needed to flip color
    NoColor,            \* The value representing "uncolored"
    NoMessage           \* The value representing "no message in transit"

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
Colors == {"Red", "Blue"}

MessageTypes == {"Query", "Reply", "Term"}

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    color,          \* [node -> color or NoColor]
    msgs,           \* Set of in‑flight messages
    pc,             \* [proc -> pc value]  (process counters)
    sample,         \* [loopProc -> SUBSET Node]  (current sample set)
    iterCount       \* [loopProc -> Nat]  (iterations completed)

(*--------------------------------------------------------------------
  Types (used in the type invariant)
--------------------------------------------------------------------*)
Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Msg == [type : {"Query", "Reply", "Term"},
        src  : Proc,
        dst  : Proc,
        payload : {NoMessage} \cup COLORS]

COLORS == Colors

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
HostOfLoop(p) == 
    LET t == CHOOSE t \in HostMapping : t.loop = p IN t.node

HostOfQuery(q) == 
    LET t == CHOOSE t \in HostMapping : t.query = q IN t.node

LoopOfNode(n) == 
    LET t == CHOOSE t \in HostMapping : t.node = n IN t.loop

QueryOfNode(n) == 
    LET t == CHOOSE t \in HostMapping : t.node = n IN t.query

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc     = [proc \in Proc |-> 
                    IF proc = "Client" THEN "Assign"
                    ELSE IF proc \in SlushLoopProcess THEN "WaitColor"
                    ELSE "ReplyLoop"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
ClientAssign ==
    /\ pc["Client"] = "Assign"
    /\ \E n \in Node :
        /\ color[n] = NoColor
        /\ LET c \in Colors IN
            /\ color' = [color EXCEPT ![n] = c]
    /\ pc' = [pc EXCEPT !["Client"] = "Assign"]
    /\ UNCHANGED <<msgs, sample, iterCount>>

LoopWaitColor(lp) ==
    /\ lp \in SlushLoopProcess
    /\ pc[lp] = "WaitColor"
    /\ color[HostOfLoop(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "SelectSample"]
    /\ UNCHANGED <<color, msgs, sample, iterCount>>

LoopSelectSample(lp) ==
    /\ lp \in SlushLoopProcess
    /\ pc[lp] = "SelectSample"
    /\ iterCount[lp] < SlushIterationCount
    /\ sample[lp] = {}               \* ensure previous sample cleared
    /\ LET otherNodes == Node \ {HostOfLoop(lp)} IN
        /\ sample' = [sample EXCEPT ![lp] = 
                       CHOOSE s \in SUBSET otherNodes : Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs \cup 
        { [type |-> "Query",
           src  |-> lp,
           dst  |-> QueryOfNode(p),
           payload |-> color[HostOfLoop(lp)]] :
               p \in sample'[lp] }
    /\ pc' = [pc EXCEPT ![lp] = "AwaitReplies"]
    /\ UNCHANGED <<color, iterCount>>

QueryReceive(q) ==
    /\ q \in SlushQueryProcess
    /\ \E m \in msgs :
        /\ m.type = "Query"
        /\ m.dst = q
    /\ LET m == CHOOSE mm \in msgs :
                /\ mm.type = "Query"
                /\ mm.dst = q
           n == HostOfQuery(q) IN
        /\ IF color[n] = NoColor THEN
               color' = [color EXCEPT ![n] = m.payload]
           ELSE
               color' = color
        /\ msgs' = msgs \ {m} \cup
            { [type |-> "Reply",
               src  |-> q,
               dst  |-> m.src,
               payload |-> color'[n]] }
    /\ UNCHANGED <<pc, sample, iterCount>>

LoopAwaitReplies(lp) ==
    /\ lp \in SlushLoopProcess
    /\ pc[lp] = "AwaitReplies"
    /\ \A q \in sample[lp] : 
        \E r \in msgs :
            /\ r.type = "Reply"
            /\ r.dst = lp
            /\ r.src = QueryOfNode(q)
    /\ LET replies == { r.payload : 
            \E r \in msgs :
               /\ r.type = "Reply"
               /\ r.dst = lp
               /\ r.src \in { QueryOfNode(p) : p \in sample[lp] } } IN
        /\ \E c \in Colors :
            Cardinality({ r \in replies : r = c }) >= PickFlipThreshold
        /\ color' = [color EXCEPT ![HostOfLoop(lp)] = 
                     CHOOSE c \in Colors :
                        Cardinality({ r \in replies : r = c }) >= PickFlipThreshold]
    /\ msgs' = msgs \ 
        { r \in msgs :
            r.type = "Reply" /\ r.dst = lp /\ r.src \in { QueryOfNode(p) : p \in sample[lp] } }
    /\ pc' = [pc EXCEPT ![lp] = 
                IF iterCount[lp] + 1 = SlushIterationCount 
                THEN "SendTerm"
                ELSE "SelectSample"]
    /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]

LoopSendTerm(lp) ==
    /\ lp \in SlushLoopProcess
    /\ pc[lp] = "SendTerm"
    /\ msgs' = msgs \cup 
        { [type |-> "Term",
           src  |-> lp,
           dst  |-> qp,
           payload |-> NoMessage] :
               qp \in SlushQueryProcess }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iterCount>>

QueryLoopExit(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess :
        \E t \in msgs :
            /\ t.type = "Term"
            /\ t.dst = q
    /\ pc' = [pc EXCEPT ![q] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iterCount>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E n \in Node : 
          /\ pc["Client"] = "Assign"
          /\ color[n] = NoColor
          /\ ClientAssign
    \/ \E lp \in SlushLoopProcess :
          /\ pc[lp] = "WaitColor"
          /\ LoopWaitColor(lp)
    \/ \E lp \in SlushLoopProcess :
          /\ pc[lp] = "SelectSample"
          /\ LoopSelectSample(lp)
    \/ \E q \in SlushQueryProcess :
          /\ QueryReceive(q)
    \/ \E lp \in SlushLoopProcess :
          /\ pc[lp] = "AwaitReplies"
          /\ LoopAwaitReplies(lp)
    \/ \E lp \in SlushLoopProcess :
          /\ pc[lp] = "SendTerm"
          /\ LoopSendTerm(lp)
    \/ \E q \in SlushQueryProcess :
          /\ pc[q] = "ReplyLoop"
          /\ QueryLoopExit(q)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iterCount>>

(*--------------------------------------------------------------------
  Safety property (type invariant)
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq 
        { [type : {"Query","Reply","Term"},
           src  : Proc,
           dst  : Proc,
           payload : {NoMessage} \cup COLORS] }
    /\ pc \in [Proc -> {"Assign","WaitColor","SelectSample","AwaitReplies",
                       "SendTerm","Done","ReplyLoop"}]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCount \in [SlushLoopProcess -> Nat]

=============================================================================