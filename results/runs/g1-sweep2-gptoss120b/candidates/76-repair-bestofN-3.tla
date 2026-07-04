---- MODULE EWD998ChanID_shiviz ----
EXTENDS EWD998ChanID, TLC

\* Init  except that  active  and  color  are restricted to TRUE and "white" to
 \* not waste time generating initial states nobody needs.
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
    \* TODO Choose some upper length or a invariant that produces a more
     \* TODO interesting behavior.  If you increase the length, don't forget
     \* TODO to also update TLC's depth parameter.
    TLCGet("level") < 666
    \* A trace ending with  terminationDetected = TRUE  that is longer than 22
     \* steps.
    \*EWD998Chan!EWD998!terminationDetected => TLCGet("level") < 23

\* Temporal logics got rid of explicit state indices.  However, when we transform
 \* counter-examples, the annoyances of handling indices re-surface.  Especially,
 \* we are dealing with *finite* prefixes of behaviors.

\* The  n \in Node  whose "variables" changed in the current step compared to
 \* the *predecessor* state.  The parameter  s  represents the current state,
 \* the parameter  t  the predecessor state.
 \* Determining whether or not a node has changed is usually easiest by
 \* introducing a prophecy variable into the spec (see  thread  variable in
 \* https://git.io/JZ0Wb).
host ==
    IF TLCGet("level") = 1 THEN Initiator
    ELSE CHOOSE n \in Node : TRUE

Alias == 
    [ Host   |-> host,
      Clock  |-> clock[host],
      active |-> active,
      color  |-> color,
      counter|-> counter,
      inbox  |-> inbox
    ]

=============================================================================