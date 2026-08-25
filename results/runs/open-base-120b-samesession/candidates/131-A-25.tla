---- MODULE MajorityProof ----
CONSTANT Value

(* Import the main majority vote specification.
   It is assumed to define the variables, Init, Next, Spec,
   and the invariants TypeOK, Correct, and Inv. *)
INSTANCE Majority WITH Value = Value

(* Expose the required identifiers for the configuration file *)
Spec   == Majority!Spec
Init   == Majority!Init
Next   == Majority!Next
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv    == Majority!Inv

====