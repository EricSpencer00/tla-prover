---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants (to be supplied in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Node,               \* Set of nodes
    SlushLoopProcess,   \* One loop process per node
    SlushQueryProcess,  \* One query process per node
    HostMapping,        \* Set of triples (loopProc, queryProc, node)
    SlushIterationCount,\* Number of iterations each loop process may perform
    SampleSetSize,      \* Size of the peer sample chosen each round
    PickFlipThreshold,  \* Minimum count of a color needed to flip
    NoColor,            \* Sentinel representing "uncolored"
    NoMessage           \* Sentinel representing "no message"

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Colors == { "Red", "Blue", NoColor }

MessageTypes == {"Query", "Reply", "Terminate"}

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    colorAssignment,    \* [node -> Colors]
    msgs,               \* set of messages currently in flight
    pc,                 \* [proc -> Nat] program counter per process
    sampleSet,          \* [loopProc -> SUBSET Node] peers sampled this round
    iterCount           \* [loopProc -> Nat] number of completed iterations

(*-----------------------------------------------------------------
  State space definition
-----------------------------------------------------------------*)
vars == << colorAssignment, msgs, pc, sampleSet, iterCount >>

(*-----------------------------------------------------------------
  Types (for the type invariant)
-----------------------------------------------------------------*)
Message == [type : {"Query", "Reply", "Terminate"},
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            payload : UNION {Colors, NoMessage}]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
LoopOf(node) == CHOOSE lp \in SlushLoopProcess : 
                   \E qp \in SlushQueryProcess : <<lp, qp, node>> \in HostMapping

QueryOf(node) == CHOOSE qp \in SlushQueryProcess :
                    \E lp \in SlushLoopProcess : <<lp, qp, node>> \in HostMapping

HostOfLoop(lp) == CHOOSE n \in Node : 
                    \E qp \in SlushQueryProcess : <<lp, qp, n>> \in HostMapping

HostOfQuery(qp) == CHOOSE n \in Node :
                     \E lp \in SlushLoopProcess : <<lp, qp, n>> \in HostMapping

TerminateSent == { lp \in SlushLoopProcess : 
                    [type |-> "Terminate", src |-> lp, dst |-> "All", payload |-> NoMessage] \in msgs }

AllTerminated == \A lp \in SlushLoopProcess : 
                   [type |-> "Terminate", src |-> lp, dst |-> "All", payload |-> NoMessage] \in msgs

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ colorAssignment = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 0]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
ClientAssign ==
    /\ pc["Client"] = 0
    /\ \E n \in Node :
          /\ colorAssignment[n] = NoColor
          /\ \E c \in {"Red", "Blue"} :
                /\ colorAssignment' = [colorAssignment EXCEPT ![n] = c]
                /\ pc' = [pc EXCEPT !["Client"] = 1]
                /\ UNCHANGED << msgs, sampleSet, iterCount >>
    /\ pc["Client"] = 1
    /\ \E n \in Node :
          /\ colorAssignment[n] # NoColor
          /\ pc' = [pc EXCEPT !["Client"] = 0]
    /\ UNCHANGED << colorAssignment, msgs, sampleSet, iterCount >>

RequireColor(lp) ==
    /\ pc[lp] = 0
    /\ LET n == HostOfLoop(lp) IN
       /\ colorAssignment[n] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = 1]
    /\ UNCHANGED << colorAssignment, msgs, sampleSet, iterCount >>

SendQuery(lp) ==
    /\ pc[lp] = 1
    /\ LET n == HostOfLoop(lp) IN
       /\ LET curColor == colorAssignment[n] IN
          /\ \E peers \in SUBSET (Node \ {n}) :
                /\ Cardinality(peers) = SampleSetSize
                /\ LET qps == { QueryOf(p) : p \in peers } IN
                     /\ msgs' = msgs \cup 
                        { [type |-> "Query", src |-> lp, dst |-> qp,
                           payload |-> curColor] : qp \in qps }
                     /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
                     /\ pc' = [pc EXCEPT ![lp] = 2]
                     /\ UNCHANGED << colorAssignment, iterCount >>
    /\ UNCHANGED << colorAssignment, msgs, sampleSet, iterCount >>

ReceiveQuery(qp) ==
    /\ pc[qp] \in {0, 2}  \* 0: idle, 2: after sending replies
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst = qp
          /\ LET n == HostOfQuery(qp) IN
                /\ IF colorAssignment[n] = NoColor
                      THEN colorAssignment' = [colorAssignment EXCEPT ![n] = m.payload]
                      ELSE UNCHANGED colorAssignment
                /\ msgs' = (msgs \ {m}) \cup 
                     { [type |-> "Reply", src |-> qp, dst |-> m.src,
                        payload |-> colorAssignment'[n]] }
                /\ pc' = [pc EXCEPT ![qp] = 1]
    /\ UNCHANGED << sampleSet, iterCount >>

CollectReplies(lp) ==
    /\ pc[lp] = 2
    /\ LET n == HostOfLoop(lp) IN
       /\ LET peers == sampleSet[lp] IN
          /\ \E replies \in SUBSET msgs :
                /\ \A m \in replies :
                      /\ m.type = "Reply"
                      /\ m.dst = lp
                      /\ m.src \in { QueryOf(p) : p \in peers }
                /\ \A p \in peers :
                      /\ [type |-> "Reply", src |-> QueryOf(p), dst |-> lp,
                          payload |-> _] \in replies
                /\ LET redCnt  == Cardinality({ m \in replies : m.payload = "Red" }) IN
                   LET blueCnt == Cardinality({ m \in replies : m.payload = "Blue" }) IN
                   LET newColor ==
                       IF redCnt >= PickFlipThreshold THEN "Red"
                       ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                       ELSE colorAssignment[n] IN
                     /\ colorAssignment' = [colorAssignment EXCEPT ![n] = newColor]
                     /\ msgs' = msgs \ replies
                     /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
                     /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
                     /\ IF iterCount'[lp] = SlushIterationCount
                          THEN pc' = [pc EXCEPT ![lp] = 3] \* go to termination
                          ELSE pc' = [pc EXCEPT ![lp] = 0] \* start next iteration
    /\ UNCHANGED << pc >>

SendTerminate(lp) ==
    /\ pc[lp] = 3
    /\ msgs' = msgs \cup { [type |-> "Terminate", src |-> lp, dst |-> "All",
                           payload |-> NoMessage] }
    /\ pc' = [pc EXCEPT ![lp] = 4]
    /\ UNCHANGED << colorAssignment, sampleSet, iterCount >>

QueryLoopExit(qp) ==
    /\ pc[qp] = 1
    /\ AllTerminated
    /\ pc' = [pc EXCEPT ![qp] = 4]
    /\ UNCHANGED << colorAssignment, msgs, sampleSet, iterCount >>

Done ==
    /\ pc["Client"] = 0
    /\ \A lp \in SlushLoopProcess : pc[lp] = 4
    /\ \A qp \in SlushQueryProcess : pc[qp] = 4
    /\ UNCHANGED vars

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : SendQuery(lp)
    \/ \E qp \in SlushQueryProcess : ReceiveQuery(qp)
    \/ \E lp \in SlushLoopProcess : CollectReplies(lp)
    \/ \E lp \in SlushLoopProcess : SendTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryLoopExit(qp)
    \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Type invariant (the only required invariant)
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ colorAssignment \in [Node -> Colors]
    /\ msgs \subseteq { [type : {"Query","Reply","Terminate"},
                        src  : (SlushLoopProcess \cup SlushQueryProcess),
                        dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"All"}),
                        payload : UNION {Colors, NoMessage}] }

=============================================================================