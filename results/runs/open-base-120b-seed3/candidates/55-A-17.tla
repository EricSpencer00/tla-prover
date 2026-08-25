---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* ----------------------------------------------------------------------
   Concrete definitions used for constant substitution by the .cfg file.
   The .cfg will bind Node   = N1,
                     initiator = I1,
                     R      = R1,
                     NoNode = NoNode (or a model value).
   ---------------------------------------------------------------------- *)

N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<"n1","n2">>, <<"n2","n1">>,
        <<"n1","n3">>, <<"n3","n1">>,
        <<"n2","n3">>, <<"n3","n2">> }
NoNode == "NoNode"

(* ----------------------------------------------------------------------
   TestSpec – the specification to be checked.
   It prints the adjacency relation at startup (via TLC's Print).
   ---------------------------------------------------------------------- *)

TestSpec == Init /\ Print(R) /\ [] [][Next]_vars

====