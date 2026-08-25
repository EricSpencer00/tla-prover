---- MODULE MCEcho ----
EXTENDS Echo

CONSTANTS Node, initiator, R, NoNode

(* concrete instances for the three‑node fully‑meshed graph *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == { <<a, b>> : a \in N1 /\ b \in N1 /\ a # b }
NoNode == "None"

(* the specification exercised by TLC *)
TestSpec == Spec

====