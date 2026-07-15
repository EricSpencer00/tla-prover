---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Constants (to be supplied in the .cfg)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop process identifiers
    SlushQueryProcess,   \* set of query process identifiers
    HostMapping,         \* set of triples <<lp, qp, n>>
    SlushIterationCount, \* total iterations each loop process must perform
    SampleSetSize,       \* size of the sampled peer set each round
    PickFlipThreshold,   \* number of matching replies needed to flip
    NoColor,             \* sentinel for “uncolored”
    NoMessage            \* sentinel used to indicate “no message” in a channel

(* ----------------------------------------------------------------------
   Derived constants
   ---------------------------------------------------------------------- *)
Nodes == Node

Colors == {1, 2}                 \* the two possible colors

Messages == {
    << "query",          lp, qp, n, c >> | 
        lp \in SlushLoopProcess /\ 
        qp \in SlushQueryProcess /\ 
        n \in Node /\ 
        c \in Colors
} \cup {
    << "reply",          lp, qp, n, c >> |
        lp \in SlushLoopProcess /\ 
        qp \in SlushQueryProcess /\ 
        n \in Node /\ 
        c \in Colors
} \cup {
    << "term",           lp >> |
        lp \in SlushLoopProcess
}

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    color,          \* [n \in Node |-> NoColor or a color from Colors]
    msgs,           \* set of in‑flight messages
    pc,             \* program counters for each process
    sample,         \* [lp \in SlushLoopProcess |-> {}]  current sample set
    iterCount       \* [lp \in SlushLoopProcess |-> 0]   completed iterations

vars == <<color, msgs, pc, sample, iterCount>>

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
HostOfLoop(lp) == 
    CHOOSE n \in Node : 
        <<lp, q, n>> \in HostMapping /\ q \in SlushQueryProcess

HostOfQuery(qp) ==
    CHOOSE n \in Node :
        <<lp, qp, n>> \in HostMapping /\ lp \in SlushLoopProcess

LoopOfNode(n) == 
    CHOOSE lp \in SlushLoopProcess :
        <<lp, qp, n>> \in HostMapping /\ qp \in SlushQueryProcess

QueryOfNode(n) == 
    CHOOSE qp \in SlushQueryProcess :
        <<lp, qp, n>> \in HostMapping /\ lp \in SlushLoopProcess

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "Init"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* client repeatedly picks an uncolored node and gives it a random color *)
ClientAssign ==
    /\ pc["client"] = "Init"
    /\ \E n \in Node :
        /\ color[n] = NoColor
        /\ c \in Colors
        /\ color' = [color EXCEPT ![n] = c]
    /\ msgs' = msgs
    /\ pc' = [pc EXCEPT !["client"] = "Assign"]
    /\ UNCHANGED << sample, iterCount >>

ClientDone ==
    /\ pc["client"] = "Assign"
    /\ color = [n \in Node |-> NoColor] => FALSE
    /\ pc' = [pc EXCEPT !["client"] = "Done"]
    /\ UNCHANGED << color, msgs, sample, iterCount >>

(* each loop process waits until its node is colored before starting *)
RequireColor ==
    /\ pc[lp] = "Init"
    /\ color[HostOfLoop(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Iterate"]
    /\ UNCHANGED << color, msgs, sample, iterCount >>
    /\ lp \in SlushLoopProcess

(* pick a random sample of peers (any subset of size SampleSetSize) *)
QuerySampleSet ==
    /\ pc[lp] = "Iterate"
    /\ sample[lp] = {}
    /\ \E s \in SUBSET (SlushQueryProcess \ {QueryOfNode(HostOfLoop(lp))}) :
        /\ Cardinality(s) = SampleSetSize
        /\ msgs' = msgs \cup { << "query", lp, qp, HostOfLoop(lp), color[HostOfLoop(lp)] >> : qp \in s}
    /\ sample' = [sample EXCEPT ![lp] = s]
    /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED << color, iterCount >>

(* query processes respond to incoming query messages *)
RespondToQuery ==
    /\ \E msg \in msgs :
        /\ msg[1] = "query"
        /\ LET lp  == msg[2]
           qp  == msg[3]
           n   == msg[4]
           c   == msg[5] IN
           /\ color[n] = NoColor => 
                color' = [color EXCEPT ![n] = c]
           /\ color' = color
           /\ msgs' = (msgs \ {msg}) \cup { << "reply", lp, qp, n, color'[n] >> }
    /\ pc' = pc
    /\ UNCHANGED << sample, iterCount >>

(* loop process tallies replies, possibly flips its node's color *)
TallyReplies ==
    /\ pc[lp] = "WaitReplies"
    /\ \E replies \in SUBSET msgs :
        /\ \A r \in replies :
            /\ r[1] = "reply"
            /\ r[2] = lp
            /\ r[3] \in sample[lp]
        /\ Cardinality(replies) = SampleSetSize
    /\ LET colorsReceived == { r[5] : r \in replies } IN
       IF \E col \in Colors :
            /\ Cardinality({ r \in replies : r[5] = col }) >= PickFlipThreshold
          THEN 
            /\ color' = [color EXCEPT ![HostOfLoop(lp)] = col]
          ELSE 
            /\ color' = color
    /\ msgs' = msgs \ { r \in msgs : r[1] = "reply" /\ r[2] = lp }
    /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
    /\ IF iterCount'[lp] = SlushIterationCount
          THEN pc' = [pc EXCEPT ![lp] = "Terminate"]
          ELSE pc' = [pc EXCEPT ![lp] = "Iterate"]
    /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ UNCHANGED << sample, iterCount >>

(* broadcast termination *)
Terminate ==
    /\ pc[lp] = "Terminate"
    /\ msgs' = msgs \cup { << "term", lp >> }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED << color, sample, iterCount >>

(* query processes exit when all loop processes have terminated *)
QueryLoopExit ==
    /\ pc[qp] = "Init"
    /\ \A lp \in SlushLoopProcess : pc[lp] = "Done"
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED << color, msgs, sample, iterCount >>

(* no‑op stuttering step *)
Stutter ==
    UNCHANGED vars

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ ClientAssign
    \/ ClientDone
    \/ \E lp \in SlushLoopProcess : RequireColor
    \/ \E lp \in SlushLoopProcess : QuerySampleSet
    \/ RespondToQuery
    \/ \E lp \in SlushLoopProcess : TallyReplies
    \/ \E lp \in SlushLoopProcess : Terminate
    \/ \E qp \in SlushQueryProcess : QueryLoopExit
    \/ Stutter

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ \A n \in Node : color[n] \in Colors \/ color[n] = NoColor
    /\ \A m \in msgs :
        (m[1] = "query" => /\ m[2] \in SlushLoopProcess /\ m[3] \in SlushQueryProcess
                                 /\ m[4] \in Node /\ m[5] \in Colors)
        \/ (m[1] = "reply" => /\ m[2] \in SlushLoopProcess /\ m[3] \in SlushQueryProcess
                                 /\ m[4] \in Node /\ m[5] \in Colors)
        \/ (m[1] = "term"  => /\ m[2] \in SlushLoopProcess)

=============================================================================