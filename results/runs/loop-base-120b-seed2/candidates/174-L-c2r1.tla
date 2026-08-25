---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS 
    Node,                    \* set of node identifiers
    SlushLoopProcess,        \* one loop process per node
    SlushQueryProcess,       \* one query process per node
    HostMapping,             \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,     \* number of iterations each loop performs
    SampleSetSize,           \* size of the sampled peer set
    PickFlipThreshold,       \* threshold for adopting a color
    NoColor,                 \* special value meaning “uncolored”
    NoMessage                \* placeholder for “no message”

(* ------------------------------------------------------------------- *)
(* Colors used by the protocol                                           *)
CONSTANTS Red, Blue
ASSUME Red # Blue

Colors == {Red, Blue}

(* ------------------------------------------------------------------- *)
(* Helper functions to map a process to its host node                    *)
HostNodeLoop(p) == 
    CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping

HostNodeQuery(q) == 
    CHOOSE n \in Node : \E p \in SlushLoopProcess : <<n, p, q>> \in HostMapping

(* ------------------------------------------------------------------- *)
(* State variables                                                       *)
VARIABLES 
    color,          \* [Node -> (Colors \cup {NoColor})]
    msgs,           \* set of in‑flight messages
    loopPC,         \* [SlushLoopProcess -> String]  program counters
    queryPC,        \* [SlushQueryProcess -> String] program counters
    sampleSet,      \* [SlushLoopProcess -> SUBSET SlushQueryProcess]
    loopIter        \* [SlushLoopProcess -> Nat]   number of completed iterations

(* ------------------------------------------------------------------- *)
(* Message definition                                                    *)
Message ==
    [type  : {"query","reply","term"},
     src   : (SlushLoopProcess \/ SlushQueryProcess),
     dst   : (SlushLoopProcess \/ SlushQueryProcess \/ "All"),
     color : (Colors \cup {NoColor})]

(* ------------------------------------------------------------------- *)
(* Initial state                                                         *)
Init ==
    /\ color      = [n \in Node |-> NoColor]
    /\ msgs       = {}
    /\ loopPC     = [p \in SlushLoopProcess |-> "awaitColor"]
    /\ queryPC    = [q \in SlushQueryProcess |-> "replyLoop"]
    /\ sampleSet  = [p \in SlushLoopProcess |-> {}]
    /\ loopIter   = [p \in SlushLoopProcess |-> 0]

(* ------------------------------------------------------------------- *)
(* Actions                                                               *)

(* Client assigns a random color to any still‑uncolored node *)
ClientAssign ==
    /\ \E n \in Node :
         /\ color[n] = NoColor
         /\ \E c \in Colors :
               /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, loopPC, queryPC, sampleSet, loopIter>>

(* Loop process waits until its host node has a color *)
RequireColor(p) ==
    /\ loopPC[p] = "awaitColor"
    /\ color[HostNodeLoop(p)] # NoColor
    /\ loopPC' = [loopPC EXCEPT ![p] = "sample"]
    /\ UNCHANGED <<color, msgs, queryPC, sampleSet, loopIter>>

(* Loop process samples peers and sends query messages *)
SamplePeers(p) ==
    /\ loopPC[p] = "sample"
    /\ LET peers == { q \in SlushQueryProcess :
                       HostNodeQuery(q) # HostNodeLoop(p) } IN
       sampleSet' = [sampleSet EXCEPT ![p] = 
           CHOOSE s \in SUBSET peers : Cardinality(s) = SampleSetSize]
    /\ \A q \in sampleSet'[p] :
         msgs' = msgs \cup {
             [type  |-> "query",
              src   |-> p,
              dst   |-> q,
              color |-> color[HostNodeLoop(p)]]
         }
    /\ loopPC' = [loopPC EXCEPT ![p] = "awaitReplies"]
    /\ UNCHANGED <<color, queryPC, loopIter>>

(* Query process handles a query, possibly adopts the queried color,
   and replies *)
RespondQuery(q) ==
    /\ queryPC[q] = "replyLoop"
    /\ \E m \in msgs :
         /\ m.type = "query"
         /\ m.dst  = q
         /\ LET srcLoop   == m.src
                hostNode  == HostNodeQuery(q)
                curColor  == color[hostNode]
                newColor  == IF curColor = NoColor THEN m.color ELSE curColor
                color'    == [color EXCEPT ![hostNode] = newColor]
                reply     == [type  |-> "reply",
                              src   |-> q,
                              dst   |-> srcLoop,
                              color |-> newColor]
            IN
               /\ msgs' = (msgs \ {m}) \cup {reply}
               /\ UNCHANGED <<loopPC, sampleSet, loopIter, queryPC>>

(* Loop process tallies replies, possibly flips its node's color,
   and either continues or terminates *)
TallyReplies(p) ==
    /\ loopPC[p] = "awaitReplies"
    /\ \A q \in sampleSet[p] :
         \E m \in msgs :
            /\ m.type = "reply"
            /\ m.dst  = p
            /\ m.src  = q
    /\ LET replies   == { m.color : m \in msgs /\ m.type = "reply" /\ m.dst = p },
           redCount   == Cardinality({c \in replies : c = Red}),
           blueCount  == Cardinality({c \in replies : c = Blue}),
           curColor   == color[HostNodeLoop(p)],
           newColor   == IF redCount >= PickFlipThreshold THEN Red
                         ELSE IF blueCount >= PickFlipThreshold THEN Blue
                         ELSE curColor
       IN
          /\ color' = [color EXCEPT ![HostNodeLoop(p)] = newColor]
          /\ loopIter' = [loopIter EXCEPT ![p] = @ + 1]
          /\ LET nextPC == IF loopIter'[p] < SlushIterationCount
                         THEN "sample"
                         ELSE "terminate" IN
                /\ loopPC' = [loopPC EXCEPT ![p] = nextPC]
          /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
          /\ msgs' = msgs \ { m \in msgs : m.type = "reply" /\ m.dst = p }
          /\ UNCHANGED queryPC

(* Loop process broadcasts a termination message and marks itself done *)
TerminateLoop(p) ==
    /\ loopPC[p] = "terminate"
    /\ msgs' = msgs \cup {
           [type |-> "term", src |-> p, dst |-> "All", color |-> NoColor]
       }
    /\ loopPC' = [loopPC EXCEPT ![p] = "done"]
    /\ UNCHANGED <<color, sampleSet, loopIter, queryPC>>

(* Query processes exit once every loop has sent a termination message *)
QueryExit(q) ==
    /\ queryPC[q] = "replyLoop"
    /\ \A p \in SlushLoopProcess :
         \E m \in msgs : m.type = "term" /\ m.dst = "All"
    /\ queryPC' = [queryPC EXCEPT ![q] = "done"]
    /\ UNCHANGED <<color, msgs, loopPC, sampleSet, loopIter>>

(* ------------------------------------------------------------------- *)
(* Combined next‑state relation                                            *)
Next ==
    \/ \E p \in SlushLoopProcess : RequireColor(p)
    \/ \E p \in SlushLoopProcess : SamplePeers(p)
    \/ \E p \in SlushLoopProcess : TallyReplies(p)
    \/ \E p \in SlushLoopProcess : TerminateLoop(p)
    \/ \E q \in SlushQueryProcess : RespondQuery(q)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ ClientAssign

(* ------------------------------------------------------------------- *)
(* Type invariant                                                         *)
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message

(* ------------------------------------------------------------------- *)
(* Specification                                                          *)
Spec == Init /\ [][Next]_<<color, msgs, loopPC, queryPC, sampleSet, loopIter>>
=============================================================================