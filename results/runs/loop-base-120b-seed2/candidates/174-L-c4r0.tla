---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop process identifiers
    SlushQueryProcess,   \* set of query process identifiers
    HostMapping,         \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* number of iterations each loop process must perform
    SampleSetSize,       \* size of the peer sample taken each round
    PickFlipThreshold,   \* threshold for adopting a color
    NoColor,             \* sentinel for “uncolored”
    NoMessage            \* sentinel for “no message” (unused but required)

(* ---------------------------------------------------------------------- *)
(* Colors used by the protocol                                             *)
Red   == "Red"
Blue  == "Blue"
Color == {Red, Blue}

(* ---------------------------------------------------------------------- *)
(* Process identifiers                                                     *)
Client  == "client"
ProcSet == Client \cup SlushLoopProcess \cup SlushQueryProcess

(* ---------------------------------------------------------------------- *)
(* Message definition                                                      *)
Message == [type  : {"query", "reply", "term"},
            src   : ProcSet,
            dst   : ProcSet,
            color : Color \cup {NoColor}]

(* ---------------------------------------------------------------------- *)
(* Helper functions for the host mapping                                   *)

LoopProc(n) == CHOOSE lp \in SlushLoopProcess :
                \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping

QueryProc(n) == CHOOSE qp \in SlushQueryProcess :
                \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

NodeOfLoop(lp) == CHOOSE n \in Node :
                  \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping

NodeOfQuery(qp) == CHOOSE n \in Node :
                   \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

(* ---------------------------------------------------------------------- *)
(* PlusCal algorithm modeling the Slush protocol                           *)

(*--algorithm SlushAlg
variables
    col    = [n \in Node |-> NoColor],
    msgs   = {},
    sample = [lp \in SlushLoopProcess |-> {}],
    iter   = [lp \in SlushLoopProcess |-> 0];

process (client = Client) {
    while (∃ n \in Node : col[n] = NoColor) {
        with n \in { n \in Node : col[n] = NoColor } do
            either
                col' = [col EXCEPT ![n] = Red]
            or
                col' = [col EXCEPT ![n] = Blue]
            end either;
        end with;
    }
}

process (lp \in SlushLoopProcess) {
    variable node \in Node;
    begin
        node := NodeOfLoop(lp);
        while (col[node] = NoColor) do
            skip;
        end while;
        while (iter[lp] < SlushIterationCount) {
            (* choose a random sample of peers *)
            with s \in SUBSET (Node \ {node}) :
                 Cardinality(s) = SampleSetSize
            do
                sample' = [sample EXCEPT ![lp] = s];
                (* send query messages to the sampled peers *)
                with n \in s do
                    let qp == QueryProc(n) in
                        msgs := msgs \cup {
                            [type  |-> "query",
                             src   |-> lp,
                             dst   |-> qp,
                             color |-> col[node]]
                        };
                    end let;
                end with;
            end with;

            (* collect replies from the sampled peers *)
            variable replies = {};
            while (Cardinality(replies) < SampleSetSize) do
                with m \in msgs :
                     /\ m.type = "reply"
                     /\ m.dst = lp
                do
                    replies := replies \cup {m};
                    msgs    := msgs \ {m};
                end with;
            end while;

            (* tally the received colors *)
            variable redCount  = Cardinality({ r \in replies : r.color = Red });
            variable blueCount = Cardinality({ r \in replies : r.color = Blue });
            if (redCount >= PickFlipThreshold) then
                col' = [col EXCEPT ![node] = Red];
            elsif (blueCount >= PickFlipThreshold) then
                col' = [col EXCEPT ![node] = Blue];
            else
                skip;
            end if;

            (* prepare for the next iteration *)
            sample' = [sample EXCEPT ![lp] = {}];
            iter'   = [iter EXCEPT ![lp] = @ + 1];
        }
        (* broadcast termination to all query processes *)
        with qp \in SlushQueryProcess do
            msgs := msgs \cup {
                [type  |-> "term",
                 src   |-> lp,
                 dst   |-> qp,
                 color |-> NoColor]
            };
        end with;
    end;
}

process (qp \in SlushQueryProcess) {
    variable node \in Node;
    begin
        node := NodeOfQuery(qp);
        while TRUE do
            either
                with m \in msgs :
                     /\ m.type = "query"
                     /\ m.dst = qp
                do
                    if (col[node] = NoColor) then
                        col' = [col EXCEPT ![node] = m.color];
                    end if;
                    msgs := msgs \cup {
                        [type  |-> "reply",
                         src   |-> qp,
                         dst   |-> m.src,
                         color |-> col[node]]
                    };
                    msgs := msgs \ {m};
                end with;
            or
                with m \in msgs :
                     /\ m.type = "term"
                     /\ m.dst = qp
                do
                    (* termination received – exit the process *)
                    exit;
                end with;
            end either;
        end while;
    end;
}
end algorithm *)

(* ---------------------------------------------------------------------- *)
(* The PlusCal translation creates the following operators: Init, Next,
   pc (program counters), and the set vars of all state variables.           *)

vars == <<col, msgs, sample, iter, pc>>

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ col \in [Node -> (Color \cup {NoColor})]
    /\ msgs \subseteq Message

====