---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,               \* set of node identifiers
    SlushLoopProcess,   \* set of loop process identifiers (one per node)
    SlushQueryProcess,  \* set of query process identifiers (one per node)
    HostMapping,        \* function [proc -> node] for all loop and query procs
    SlushIterationCount,\* total number of iterations each loop process must run
    SampleSetSize,      \* size of the peer sample each iteration
    PickFlipThreshold,  \* threshold for adopting a color
    NoColor,            \* sentinel value meaning "uncolored"
    NoMessage           \* sentinel value meaning "no pending message"

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
LoopProcs  == SlushLoopProcess
QueryProcs == SlushQueryProcess
AllProcs   == LoopProcs \cup QueryProcs

\* ----------------------------------------------------------------------
\* Message definitions
\* ----------------------------------------------------------------------
Message == 
    [type : {"Query", "Reply", "Terminate"},
     src  : AllProcs,
     dst  : AllProcs,
     payload : {NoColor} \cup Node]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,        \* [node -> color] current color of each node
    msgs,         \* set of in‑flight messages
    pc,           \* [proc -> pc] program counter (state) of each process
    sample,       \* [loopProc -> SUBSET Node] current sample set for each loop proc
    iterCount,    \* [loopProc -> Nat] number of iterations completed so far
    clientDone    \* Boolean indicating the client has finished assigning colors

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

IsLoop(p)   == p \in LoopProcs
IsQuery(p)  == p \in QueryProcs
NodeOf(p)   == HostMapping[p]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc = [p \in AllProcs |-> 
                IF IsLoop(p) THEN "WaitColor"
                ELSE "ReplyLoop"]
    /\ sample    = [lp \in LoopProcs |-> {}]
    /\ iterCount = [lp \in LoopProcs |-> 0]
    /\ clientDone = FALSE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a color to an uncolored node
ClientAssign ==
    /\ ~clientDone
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ LET col == CHOOSE c \in Colors : TRUE IN
                /\ color' = [color EXCEPT ![n] = col]
                /\ UNCHANGED <<msgs, pc, sample, iterCount>>
    /\ IF \A n \in Node : color[n] # NoColor
       THEN clientDone' = TRUE
       ELSE clientDone' = clientDone

\* 2. Loop process waits for its node to be colored
RequireColor(lp) ==
    /\ pc[lp] = "WaitColor"
    /\ color[NodeOf(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "DoSample"]
    /\ UNCHANGED <<color, msgs, sample, iterCount, clientDone>>

\* 3. Loop process sends a query to a random sample of peers
SendQuery(lp) ==
    /\ pc[lp] = "DoSample"
    /\ \LET candidates == Node \ {NodeOf(lp)} IN
          /\ sampleSet == CHOOSE s \in SUBSET candidates :
                             Cardinality(s) = SampleSetSize
    /\ msgs' = msgs \cup { [type |-> "Query",
                            src  |-> lp,
                            dst  |-> queryProc,
                            payload |-> color[NodeOf(lp)] ] :
                            queryProc \in { HostMapping^{-1}[n] :
                                            n \in sampleSet /\ n # NodeOf(lp) } }
    /\ sample' = [sample EXCEPT ![lp] = sampleSet]
    /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED <<color, iterCount, clientDone>>

\* 4. Query process receives a query, possibly adopts the color, and replies
RespondQuery(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst  = qp
          /\ LET n == NodeOf(qp) IN
               /\ IF color[n] = NoColor
                  THEN color' = [color EXCEPT ![n] = m.payload]
                  ELSE UNCHANGED color
               /\ reply == [type |-> "Reply",
                           src  |-> qp,
                           dst  |-> m.src,
                           payload |-> color'[n]]
               /\ msgs' = (msgs \ {m}) \cup {reply}
    /\ UNCHANGED <<pc, sample, iterCount, clientDone>>

\* 5. Loop process tallies replies; may flip its node's color
TallyAndFlip(lp) ==
    /\ pc[lp] = "WaitReplies"
    /\ \E replies \in SUBSET msgs :
          /\ \A r \in replies :
                /\ r.type = "Reply"
                /\ r.dst  = lp
          /\ \A r \in replies :
                /\ r.src \in { HostMapping^{-1}[n] : n \in sample[lp] }
          /\ /\* all expected replies have been received
                /\ Cardinality(replies) = SampleSetSize
          /\ LET node == NodeOf(lp) IN
                /\ redCount  == Cardinality({r \in replies : r.payload = "Red"})
                /\ blueCount == Cardinality({r \in replies : r.payload = "Blue"})
                /\ newColor ==
                     IF redCount >= PickFlipThreshold THEN "Red"
                     ELSE IF blueCount >= PickFlipThreshold THEN "Blue"
                     ELSE color[node]
                /\ color' = [color EXCEPT ![node] = newColor]
          /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
          /\ msgs' = msgs \ replies
          /\ IF iterCount[lp] + 1 = SlushIterationCount
             THEN pc' = [pc EXCEPT ![lp] = "Terminate"]
             ELSE pc' = [pc EXCEPT ![lp] = "DoSample"]
          /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ UNCHANGED <<clientDone>>

\* 6. Loop process broadcasts a termination message
BroadcastTerminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ msgs' = msgs \cup { [type |-> "Terminate",
                            src  |-> lp,
                            dst  |-> qp,
                            payload |-> NoMessage] :
                            qp \in QueryProcs }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iterCount, clientDone>>

\* 7. Query process exits when all loop processes have terminated
QueryExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \A lp \in LoopProcs : pc[lp] = "Done"
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iterCount, clientDone>>

\* 8. Stuttering step to avoid deadlock
Stutter ==
    UNCHANGED <<color, msgs, pc, sample, iterCount, clientDone>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ \E lp \in LoopProcs : RequireColor(lp)
    \/ \E lp \in LoopProcs : SendQuery(lp)
    \/ \E qp \in QueryProcs : RespondQuery(qp)
    \/ \E lp \in LoopProcs : TallyAndFlip(lp)
    \/ \E lp \in LoopProcs : BroadcastTerminate(lp)
    \/ \E qp \in QueryProcs : QueryExit(qp)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iterCount, clientDone>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ pc \in [AllProcs -> {"WaitColor", "DoSample", "WaitReplies",
                           "Terminate", "Done", "ReplyLoop"}]
    /\ sample \in [LoopProcs -> SUBSET Node]
    /\ iterCount \in [LoopProcs -> Nat]
    /\ clientDone \in BOOLEAN

TypeInvariant == TypeOK

\* ----------------------------------------------------------------------
\* Liveness (optional, not exported as an invariant)
\* ----------------------------------------------------------------------
Termination == <> (pc = [AllProcs -> "Done"])

=============================================================================