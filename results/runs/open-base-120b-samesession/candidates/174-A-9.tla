---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  CONSTANTS (to be supplied by the .cfg file)                           *)
(***************************************************************************)
CONSTANTS
    Node,               \* the set of node identifiers
    SlushLoopProcess,   \* the set of loop process identifiers
    SlushQueryProcess,  \* the set of query process identifiers
    HostMapping,        \* [Node -> [loop |-> SlushLoopProcess,
                         \*           query |-> SlushQueryProcess]]
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold,
    NoColor,
    NoMessage

(***************************************************************************)
(*  Derived constants                                                      *)
(***************************************************************************)
Colors == {"Red", "Blue"}               \* the two possible opinions
MsgType == {"Query", "Reply", "Terminate"}

Message == [type   : MsgType,
            from   : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
            to     : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"} \cup {"All"}),
            color  : (Colors \cup {NoColor, NoMessage})]

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES
    color,          \* [Node -> (Colors \cup {NoColor})]
    msgs,           \* set of Message
    pc,             \* [proc -> Nat]   (proc ranges over all processes)
    sample,         \* [SlushLoopProcess -> SUBSET Node]  (current sample set)
    iter            \* [SlushLoopProcess -> Nat]          (iterations done)

\* Helper functions ---------------------------------------------------------
NodeOfLoop(lp) == CHOOSE n \in Node : HostMapping[n].loop = lp
NodeOfQuery(qp) == CHOOSE n \in Node : HostMapping[n].query = qp

AllProcs == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

(***************************************************************************)
(*  Initialization                                                         *)
(***************************************************************************)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in AllProcs |-> 0]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

(* 1. Client assigns a color to an uncolored node *)
ClientAssign ==
    /\ pc["Client"] = 0
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ \E c \in Colors :
                /\ color' = [color EXCEPT ![n] = c]
                /\ pc'    = [pc EXCEPT !["Client"] = 0]  \* client stays ready for next assignment
                /\ UNCHANGED <<msgs, sample, iter>>
    \/  \* No uncolored node left – client does nothing
        /\ \A n \in Node : color[n] # NoColor
        /\ UNCHANGED <<color, msgs, pc, sample, iter>>

(* 2. Loop process waits until its host node is colored *)
LoopRequireColor(lp) ==
    /\ pc[lp] = 0
    /\ color[NodeOfLoop(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = 1]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(* 3. Loop process samples a set of peers and sends queries *)
LoopSample(lp) ==
    /\ pc[lp] = 1
    /\ sample[lp] = {}
    /\ \E S \subseteq Node \ {NodeOfLoop(lp)} :
          /\ Cardinality(S) = SampleSetSize
          /\ LET qryMsgs == { [type  |-> "Query",
                               from  |-> lp,
                               to    |-> HostMapping[n].query,
                               color |-> color[NodeOfLoop(lp)] ] :
                              n \in S }
             IN
                 /\ msgs'   = msgs \cup qryMsgs
                 /\ sample' = [sample EXCEPT ![lp] = S]
                 /\ pc'     = [pc EXCEPT ![lp] = 2]
                 /\ UNCHANGED <<color, iter>>

(* 4. Query process receives a query, possibly adopts the color, and replies *)
QueryRespond(qp) ==
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.to   = qp
    LET n == NodeOfQuery(qp)
        recvColor == m.color
        curColor  == color[n]
        newColor  == IF curColor = NoColor THEN recvColor ELSE curColor
        replyMsg  == [type  |-> "Reply",
                      from  |-> qp,
                      to    |-> m.from,
                      color |-> newColor]
    IN
        /\ color' = [color EXCEPT ![n] = newColor]
        /\ msgs'  = (msgs \ {m}) \cup {replyMsg}
        /\ UNCHANGED <<pc, sample, iter>>

(* 5. Loop process tallies replies and possibly flips its own color *)
LoopTally(lp) ==
    /\ pc[lp] = 2
    /\ sample[lp] # {}
    /\ \A n \in sample[lp] :
          \E m \in msgs :
               /\ m.type = "Reply"
               /\ m.to   = lp
               /\ m.from = HostMapping[n].query
    LET reds   == Cardinality({ m \in msgs :
                                 m.type = "Reply" /\ m.to = lp /\ m.color = "Red" })
        blues  == Cardinality({ m \in msgs :
                                 m.type = "Reply" /\ m.to = lp /\ m.color = "Blue" })
        curN   == NodeOfLoop(lp)
        newCol == IF reds >= PickFlipThreshold THEN "Red"
                 ELSE IF blues >= PickFlipThreshold THEN "Blue"
                 ELSE color[curN]
        nextIter == @ + 1
    IN
        /\ color' = [color EXCEPT ![curN] = newCol]
        /\ msgs'  = msgs \ { m \in msgs :
                               m.type = "Reply" /\ m.to = lp }
        /\ sample' = [sample EXCEPT ![lp] = {}]
        /\ iter'   = [iter EXCEPT ![lp] = nextIter]
        /\ IF nextIter = SlushIterationCount
              THEN pc' = [pc EXCEPT ![lp] = 3]   \* go to termination broadcast
              ELSE pc' = [pc EXCEPT ![lp] = 0]   \* start next round
        /\ UNCHANGED <<>>

(* 6. Loop process broadcasts termination *)
LoopTerminate(lp) ==
    /\ pc[lp] = 3
    /\ msgs' = msgs \cup { [type |-> "Terminate",
                            from |-> lp,
                            to   |-> "All",
                            color|-> NoMessage] }
    /\ pc' = [pc EXCEPT ![lp] = 4]            \* terminated
    /\ UNCHANGED <<color, sample, iter>>

(* 7. Query processes exit when all loop processes have terminated *)
QueryExit(qp) ==
    /\ pc[qp] = 0
    /\ \A lp \in SlushLoopProcess :
          \E m \in msgs : m.type = "Terminate" /\ m.from = lp
    /\ pc' = [pc EXCEPT ![qp] = 1]            \* exited
    /\ UNCHANGED <<color, msgs, sample, iter>>

(***************************************************************************)
(*  Next-state relation                                                    *)
(***************************************************************************)
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : LoopRequireColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopSample(lp)
    \/ \E qp \in SlushQueryProcess : QueryRespond(qp)
    \/ \E lp \in SlushLoopProcess : LoopTally(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)
vars == <<color, msgs, pc, sample, iter>>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Type invariant                                                         *)
(***************************************************************************)
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ \A m \in msgs :
          IF m.type = "Query"    THEN m.color \in (Colors \cup {NoColor})
          ELSE IF m.type = "Reply"   THEN m.color \in (Colors \cup {NoColor})
          ELSE IF m.type = "Terminate" THEN m.color = NoMessage
          ELSE FALSE

=============================================================================