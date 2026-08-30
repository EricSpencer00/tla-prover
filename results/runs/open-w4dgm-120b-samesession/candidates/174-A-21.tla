---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

\* Loop processes consult query processes (peers) and adopt a supermajority
\* color in each round; query processes simply echo or adopt-on-first-contact.

Message == [typ : {"query", "reply", "stop"}, from : Node, to : Node,
            color : {NoColor, "red", "blue"}]

VARIABLES nodeColor, msgs, loopPC, pickPC, sample, iterations

vars == <<nodeColor, msgs, loopPC, pickPC, sample, iterations>>

\* The set of processes hosted on a node, derived from HostMapping.
Hosted(n) == {p \in HostMapping : p[2] = n}

QueryHost(q) == CHOOSE n \in Node : <<q, n>> \in Hosted

LoopHost(lp) == CHOOSE n \in Node : <<lp, n>> \in Hosted

TypeOK ==
  /\ nodeColor \in [Node -> {NoColor, "red", "blue"}]
  /\ msgs \subseteq Message
  /\ loopPC \in [SlushLoopProcess -> {"awaitColor", "sampling", "done"}]
  /\ pickPC \in [SlushQueryProcess -> {"replying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ loopPC = [lp \in SlushLoopProcess |-> "awaitColor"]
  /\ pickPC = [q \in SlushQueryProcess |-> "replying"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iterations = [lp \in SlushLoopProcess |-> 0]

\* Client hands an uncolored node its first color -- this is the only place
\* the network's color space is introduced, and it fires once per node.
AssignColor ==
  /\ \E n \in Node, c \in {"red", "blue"} :
       /\ nodeColor[n] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, loopPC, pickPC, sample, iterations>>

RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ loopPC[lp] = "awaitColor"
       /\ nodeColor[LoopHost(lp)] # NoColor
       /\ loopPC' = [loopPC EXCEPT ![lp] = "sampling"]
  /\ UNCHANGED <<nodeColor, msgs, pickPC, sample, iterations>>

QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ loopPC[lp] = "sampling"
       /\ sample[lp] = {}
       /\ Cardinality(sample[lp]) < SampleSetSize
       /\ \E q \in SlushQueryProcess :
            /\ <<q, QueryHost(q)>> \notin msgs
            /\ msgs' = msgs \cup {[typ |-> "query", from |-> LoopHost(lp),
                                   to |-> QueryHost(q), color |-> nodeColor[LoopHost(lp)]]}
            /\ sample' = [sample EXCEPT ![lp] = sample[lp] \cup {q}]
  /\ UNCHANGED <<nodeColor, loopPC, pickPC, iterations>>

\* Query processes adopt on first contact, then always reflect their host's
\* current color back to the requesting loop.
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.typ = "query"
       /\ msgs' = msgs \ {m} \cup {[typ |-> "reply", from |-> m.from, to |-> m.to,
                                   color |-> IF nodeColor[m.to] = NoColor
                                             THEN m.color ELSE nodeColor[m.to]]}
       /\ nodeColor' = [nodeColor EXCEPT ![m.to] = IF nodeColor[m.to] = NoColor
                                                     THEN m.color ELSE nodeColor[m.to]]
  /\ UNCHANGED <<loopPC, pickPC, sample, iterations>>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ loopPC[lp] = "sampling"
       /\ sample[lp] # {}
       /\ Cardinality(sample[lp]) = SampleSetSize
       /\ \A q \in sample[lp] : <<q, LoopHost(lp)>> \in msgs
       /\ LET tally == [c \in {"red", "blue"} |-> Cardinality({q \in sample[lp] :
                                     [typ |-> "reply", from |-> LoopHost(lp),
                                      to |-> QueryHost(q), color |-> c] \cap msgs})]
          IN nodeColor' = [nodeColor EXCEPT ![LoopHost(lp)] =
                             IF tally["red"] >= PickFlipThreshold THEN "red"
                             ELSE IF tally["blue"] >= PickFlipThreshold THEN "blue"
                             ELSE nodeColor[LoopHost(lp)]]
       /\ msgs' = msgs \ {[typ |-> "reply", from |-> LoopHost(lp), to |-> QueryHost(q), color |-> c] :
                           q \in sample[lp], c \in {"red", "blue"}}
       /\ sample' = [sample EXCEPT ![lp] = {}]
       /\ iterations' = [iterations EXCEPT ![lp] = IF iterations[lp] < SlushIterationCount
                                                THEN @ + 1 ELSE @]
       /\ loopPC' = IF iterations[lp] = SlushIterationCount
                    THEN [loopPC EXCEPT ![lp] = "done"]
                    ELSE loopPC
  /\ UNCHANGED pickPC

\* Loop processes broadcast termination when fully spent; query processes
\* leave their reply loop only once every loop process is done.
LoopTermination ==
  /\ \E lp \in SlushLoopProcess :
       /\ loopPC[lp] = "sampling"
       /\ iterations[lp] = SlushIterationCount
       /\ loopPC' = [loopPC EXCEPT ![lp] = "done"]
       /\ msgs' = msgs \cup {[typ |-> "stop", from |-> LoopHost(lp), to |-> LoopHost(lp), color |-> NoColor]}
  /\ UNCHANGED <<nodeColor, pickPC, sample, iterations>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pickPC[q] = "replying"
       /\ \A lp \in SlushLoopProcess : loopPC[lp] = "done"
       /\ pickPC' = [pickPC EXCEPT ![q] = "done"]
  /\ UNCHANGED <<nodeColor, msgs, loopPC, sample, iterations>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ SF_vars(AssignColor) /\ SF_vars(RequireColor) /\ SF_vars(QuerySampleSet)
        /\ SF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
        /\ SF_vars(LoopTermination) /\ SF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == <>(\A lp \in SlushLoopProcess : loopPC[lp] = "done")

====