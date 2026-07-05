---- MODULE EWD998ChanID_shiviz ----
EXTENDS EWD998ChanID, TLC, Json

\* Init except that active and color are restricted to TRUE and "white" to not waste time generating initial states nobody needs.
MCInit ==
  (* Each node maintains a (local) vector clock *)
  (* https://en.wikipedia.org/wiki/Vector_clock *)
  /\ clock = [ n \in Node |-> IF n = Initiator 
                THEN [ m \in Node |-> IF m = Initiator THEN 1 ELSE 0 ]
                ELSE [ m \in Node |-> 0 ] ]
  (* Rule 0 *)
  /\ counter = [n \in Node |-> 0] \* c properly initialized
  /\ inbox = [n \in Node |-> IF n = Initiator 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> clock[n] ] >> 
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *)
  \* Reduce the number of initial states. 
  /\ active \in [Node -> {TRUE}]
  /\ color \in [Node -> {"white"}]

Inv ==
    TLCGet("level") < 666

host ==
    LET None == "--" \* This should be a model value:  CHOOSE n : n \notin Node
        lvl == TLCGet("level")
        trc == Trace
    IN IF lvl = 1 THEN Initiator
       ELSE CHOOSE n \in Node:
            trc[lvl].clock[n] # trc[lvl-1].clock[n]

Alias == 
    [
        Host |-> host
        ,Clock |-> ToJsonObject(clock[host])
        
        ,active |-> active
        ,color |-> color
        ,counter |-> counter
        ,inbox |-> inbox
    ]

====