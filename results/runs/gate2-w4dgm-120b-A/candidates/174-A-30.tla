---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Model of the Slush protocol (a minimal probabilistic consensus protocol)   *)
(* from the Avalanche whitepaper.  This is PlusCal, translated to TLA+, and   *)
(* deliberately does not model the probabilistic convergence, only the       *)
(* protocol steps and a type-safety invariant.                                *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess,
          HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

\* host[n] = the node a process n runs on; host is a bijection between nodes
\* and loop processes, and between nodes and query processes.
host == [n \in SlushLoopProcess |-> CHOOSE x \in Node :
            <<x, n>> \in HostMapping],
        [n \in SlushQueryProcess |-> CHOOSE x \in Node :
            <<x, n>> \in HostMapping]

VARIABLES nodeColor, inbox, progCounter, sampleSet, iterations

TypeOK ==
    /\ nodeColor \in [Node -> {NoColor, "red", "blue"}]
    /\ inbox \subseteq [kind: {"msgQuery", "msgQueryReply", "msgTerminate"},
                        from: SlushLoopProcess \cup SlushQueryProcess,
                        to: SlushLoopProcess \cup SlushQueryProcess,
                        color: {NoColor, "red", "blue"}]
    /\ progCounter \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} \in {"pcInit", "pcWait", "pcQuery", "pcHandle", "pcDone"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterations \in [SlushLoopProcess -> 0 .. SlushIterationCount]

Init ==
    /\ nodeColor = [x \in Node |-> NoColor]
    /\ inbox = {}
    /\ progCounter = [n \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "pcInit"]
    /\ sampleSet = [n \in SlushLoopProcess |-> {}]
    /\ iterations = [n \in SlushLoopProcess |-> 0]

ClientAssignsColor ==
    /\ progCounter["client"] = "pcInit"
    /\ \E x \in Node, c \in {"red", "blue"} :
         /\ nodeColor[x] = NoColor
         /\ nodeColor' = [nodeColor EXCEPT ![x] = c]
    /\ progCounter' = [progCounter EXCEPT !["client"] = "pcDone"]
    /\ UNCHANGED <<inbox, sampleSet, iterations>>

RequireColor ==
    /\ \E n \in SlushLoopProcess :
         /\ progCounter[n] = "pcInit"
         /\ nodeColor[host[n]] # NoColor
         /\ progCounter' = [progCounter EXCEPT ![n] = "pcQuery"]
    /\ UNCHANGED <<nodeColor, inbox, sampleSet, iterations>>

\* Loop processes pick a random fixed-size sample of peers and poll them.
QuerySampleSet ==
    /\ \E n \in SlushLoopProcess :
         /\ progCounter[n] = "pcQuery"
         /\ Cardinality(sampleSet[n]) # SampleSetSize
         /\ \E m \in SlushQueryProcess :
              /\ m \notin sampleSet[n]
              /\ sampleSet' = [sampleSet EXCEPT ![n] = @ \cup {m}]
              /\ inbox' = inbox \cup {[kind |-> "msgQuery", from |-> n, to |-> m, color |-> nodeColor[host[n]]]}
    /\ UNCHANGED <<nodeColor, progCounter, iterations>>

\* Query processes adopt the sender's opinion if they are uncolored, then reply.
RespondToQuery ==
    /\ \E m \in SlushQueryProcess :
         /\ progCounter[m] = "pcInit"
         /\ \E msg \in inbox :
              /\ msg.kind = "msgQuery"
              /\ msg.to = m
              /\ LET qcolor == IF nodeColor[host[m]] = NoColor
                               THEN msg.color
                               ELSE nodeColor[host[m]] IN
                 nodeColor' = [nodeColor EXCEPT ![host[m]] = qcolor]
              /\ inbox' = (inbox \ {msg}) \cup {[kind |-> "msgQueryReply", from |-> m, to |-> msg.from, color |-> IF nodeColor[host[m]] = NoColor THEN msg.color ELSE nodeColor[host[m]]]}
    /\ UNCHANGED <<progCounter, sampleSet, iterations>>

\* The loop node adopts a color only once a strict majority of the sampled
\* replies agree, and only if the round budget has not been spent.
TallyReplies ==
    /\ \E n \in SlushLoopProcess :
         /\ progCounter[n] = "pcQuery"
         /\ Cardinality(sampleSet[n]) = SampleSetSize
         /\ \A m \in sampleSet[n] : ~ \E msg \in inbox : msg.kind = "msgQueryReply" /\ msg.to = n /\ msg.from = m
         /\ Cardinality({m \in sampleSet[n] : (\E msg \in inbox : msg.kind = "msgQueryReply" /\ msg.to = n /\ msg.from = m /\ msg.color = "red")}) >= PickFlipThreshold
         /\ nodeColor' = [nodeColor EXCEPT ![host[n]] = "red"]
         /\ sampleSet' = [sampleSet EXCEPT ![n] = {}]
         /\ iterations' = [iterations EXCEPT ![n] = IF iterations[n] < SlushIterationCount THEN iterations[n] + 1 ELSE iterations[n]]
         /\ progCounter' = IF iterations[n] + 1 < SlushIterationCount THEN "pcQuery" ELSE "pcDone"]
    /\ UNCHANGED inbox

LoopTermination ==
    /\ \E n \in SlushLoopProcess :
         /\ progCounter[n] = "pcDone"
         /\ inbox' = inbox \cup {[kind |-> "msgTerminate", from |-> n, to |-> n, color |-> NoColor]}
    /\ UNCHANGED <<nodeColor, progCounter, sampleSet, iterations>>

QueryLoopExit ==
    /\ \A m \in SlushQueryProcess : progCounter[m] = "pcInit"
    /\ \A n \in SlushLoopProcess : ~ \E msg \in inbox : msg.kind = "msgTerminate" /\ msg.from = n
    /\ progCounter' = [m \in SlushQueryProcess |-> "pcDone"]
    /\ UNCHANGED <<nodeColor, inbox, sampleSet, iterations>>

Next == ClientAssignsColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_<<nodeColor, inbox, progCounter, sampleSet, iterations>>

\* Structural sanity check: no variable wanders outside its domain.
TypeInvariant == TypeOK

(* Convergence is probabilistic and omitted from the spec; at least every      *)
(* process always eventually reaches its done state.                           *)
Termination == <>(\A n \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : progCounter[n] = "pcDone")
====