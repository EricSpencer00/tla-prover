---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority WITH Value <- Value

(* The complete specification: initial condition and next‑state relation. *)
Spec == Init /\ [][Next]_vars

====