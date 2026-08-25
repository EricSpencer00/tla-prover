---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Node, 
    SlushLoopProcess, 
    SlushQueryProcess, 
    HostMapping,
    SlushIterationCount, 
    SampleSetSize, 
    PickFlipThreshold,
    NoColor, 
    NoMessage

\* ----------------------------------------------------------------------
\* Derived sets and helper functions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

Message == [type  : {"query", "reply", "term"},
            src   : (SlushLoopProcess \cup SlushQueryProcess),
            dst   : (SlushLoopProcess \cup SlushQueryProcess),
            color : (Colors \cup {NoColor})]

LoopNode == [p \in SlushLoopProcess |-> 
                CHOOSE n \in Node : <<p, _, n>> \in HostMapping]

QueryNode == [q \in SlushQueryProcess |-> 
                 CHOOSE n \in Node : <<_, q, n>> \in HostMapping]

\* ----------------------------------------------------------------------
\* PlusCal algorithm
\* ----------------------------------------------------------------------
(*--algorithm Slush
variables
    colors = [n \in Node |-> NoColor],
    msgs   = {},
    sample = [p \in SlushLoopProcess |-> {}],
    iter   = [p \in SlushLoopProcess |-> 0],
    clientDone = FALSE;

process (client = {"client"}) {
    while (\E n \in Node : colors[n] = NoColor) {
        with n \in { n \in Node : colors[n] = NoColor } do
            with c \in Colors do
                colors := [colors EXCEPT ![n] = c];
            end with;
        end with;
    };
    clientDone := TRUE;
}

process (Loop = SlushLoopProcess) {
    variable n;
    n := LoopNode[self];
    await colors[n] # NoColor;
    while (iter[self] < SlushIterationCount) {
        with s \in SUBSET (Node \ {n}) :
                 Cardinality(s) = SampleSetSize
        do
            sample := [sample EXCEPT ![self] = s];
            \* send query messages to sampled peers
            with q \in { q \in SlushQueryProcess : QueryNode[q] \in s } do
                msgs := msgs \cup {
                    [type  |-> "query",
                     src   |-> self,
                     dst   |-> q,
                     color |-> colors[n]]
                };
            end with;
            \* wait for replies from all sampled peers
            await \A q \in { q \in SlushQueryProcess : QueryNode[q] \in s } :
                     \E m \in msgs :
                         m.type = "reply" /\ m.src = q /\ m.dst = self;
            \* tally replies
            let replies == { m \in msgs :
                               m.type = "reply" /\ m.dst = self /\
                               m.src \in { q \in SlushQueryProcess : QueryNode[q] \in s } } in
                let redCnt  == Cardinality({ m \in replies : m.color = "Red" }) in
                    blueCnt == Cardinality({ m \in replies : m.color = "Blue" }) in
                    if redCnt >= PickFlipThreshold then
                        colors := [colors EXCEPT ![n] = "Red"];
                    elsif blueCnt >= PickFlipThreshold then
                        colors := [colors EXCEPT ![n] = "Blue"];
                    else
                        skip;
                    end if;
                end let;
            \* clean up replies and advance iteration
            msgs := msgs \ { m \in msgs : m.type = "reply" /\ m.dst = self };
            sample := [sample EXCEPT ![self] = {}];
            iter[self] := iter[self] + 1;
        end with;
    };
    \* broadcast termination to all query processes
    with q \in SlushQueryProcess do
        msgs := msgs \cup {
            [type  |-> "term",
             src   |-> self,
             dst   |-> q,
             color |-> NoMessage]
        };
    end with;
}

process (Query = SlushQueryProcess) {
    variable n;
    n := QueryNode[self];
    while TRUE do
        await \E m \in msgs : m.dst = self;
        with m \in { m \in msgs : m.dst = self } do
            if m.type = "query" then
                if colors[n] = NoColor then
                    colors := [colors EXCEPT ![n] = m.color];
                end if;
                msgs := msgs \cup {
                    [type  |-> "reply",
                     src   |-> self,
                     dst   |-> m.src,
                     color |-> colors[n]]
                };
            elsif m.type = "term" then
                skip;
            end if;
            msgs := msgs \ { m };
        end with;
    end while;
}
end algorithm; *)

\* ----------------------------------------------------------------------
\* TLA+ wrapper around the PlusCal generated actions
\* ----------------------------------------------------------------------
VARIABLES colors, msgs, sample, iter, clientDone

Init == Slush!Init
Next == Slush!Next

Spec == Init /\ [][Next]_<<colors, msgs, sample, iter, clientDone>>

TypeInvariant ==
    /\ colors \in [Node -> (Colors \cup {NoColor})]
    /\ msgs   \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [SlushLoopProcess -> Nat]
    /\ clientDone \in BOOLEAN

====