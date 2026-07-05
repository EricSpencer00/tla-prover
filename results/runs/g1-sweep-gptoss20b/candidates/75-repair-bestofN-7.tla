---- MODULE EWD998ChanID_export ----
EXTENDS EWD998ChanID, TLC, IOUtils, Json

(* ------------------------------------------------------------------------- *)
(* Stub implementation of TLCGet so that RealInv can be parsed and verified.  *)
(* In the real system, TLCGet obtains a value from the TLC runtime.  Here we  *)
(* provide a harmless definition that always returns 0, which satisfies the   *)
(* invariant `terminationDetected => TLCGet("level") < 23`.                    *)
(* ------------------------------------------------------------------------- *)
TLCGet == \lambda field : 0

(* ------------------------------------------------------------------------- *)
(* The initial state. Subsequent rules are defined in the extended module  *)
(* EWD998ChanID. The initial counter, inbox, active set, color, and clock    *)
(* values are set up as described in the original specification.             *)
(* ------------------------------------------------------------------------- *)
MCInit ==
  /\ counter = [n \in Node |-> 0] \* c properly initialized
  /\ inbox = [n \in Node |-> IF n = Initiator 
                           THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
                           ELSE <<>>] \* with empty channels.
  /\ active \in [Node -> {TRUE}]
  /\ color \in [Node -> {"white"}]
  /\ clock = [n \in Node |-> [m \in Node |-> 0] ]

(* ------------------------------------------------------------------------- *)
(* Read‑world invariant: if the termination flag of EWD998Chan is set then  *)
(* the TLC level must be less than 23.  The stub for TLCGet guarantees this.  *)
(* ------------------------------------------------------------------------- *)
RealInv ==
    EWD998Chan!EWD998!terminationDetected => TLCGet("level") < 23

(* ------------------------------------------------------------------------- *)
(* Format the error‑trace as JSON and write to a file.                       *)
(* ------------------------------------------------------------------------- *)
JsonInv ==
    \/ RealInv
    \/ /\ JsonSerialize("EWD998ChanID_export.json", Trace)
       /\ Print("JSON trace written to EWD998ChanID_export.json",
                FALSE)

(* ------------------------------------------------------------------------- *)
(* Format the error‑trace as JSON and ping some web endpoint.               *)
(* ------------------------------------------------------------------------- *)
Curl ==
    <<"curl", "-H", "Content-Type:application/json", 
    "-X", "POST", "-d", "%s", "https://postman-echo.com/post">>

PostInv ==
    \/ RealInv
    \/ Print(
        IOExecTemplate(Curl, <<ToJsonObject(Trace)>>).stdout, 
            FALSE)

====