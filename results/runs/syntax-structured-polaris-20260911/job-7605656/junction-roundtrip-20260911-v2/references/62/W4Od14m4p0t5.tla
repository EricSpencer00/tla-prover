---- MODULE W4Od14m4p0t5 ----
EXTENDS Naturals

CONSTANTS DroneOne, DroneTwo, QueueBound, MaxPreempts, NoDrone

Drones == {DroneOne, DroneTwo}

ASSUME ( (DroneOne # DroneTwo)
        /\  (NoDrone \notin Drones)
        /\  (QueueBound \in Nat /\ QueueBound > 0)
        /\  (MaxPreempts \in Nat))

VARIABLES uplink, sending, buffered, asking, preemptsLeft

vars == <<uplink, sending, buffered, asking, preemptsLeft>>

TypeOK ==
  ( (uplink \in Drones \cup {NoDrone})
   /\  (sending \subseteq Drones)
   /\  (buffered \in [Drones -> 0 .. QueueBound])
   /\  (asking \subseteq Drones)
   /\  (preemptsLeft \in 0 .. MaxPreempts))

OnlyTheUplinkHolderTransmits ==
  ( (sending \subseteq {uplink})
   /\  (\A d \in sending : buffered[d] > 0))

Init ==
  ( (uplink = NoDrone)
   /\  (sending = {})
   /\  (buffered = [d \in Drones |-> 0])
   /\  (asking = {})
   /\  (preemptsLeft = MaxPreempts))

BufferFrame(d) ==
  ( (buffered[d] < QueueBound)
   /\  (buffered' = [buffered EXCEPT ![d] = @ + 1])
   /\  (UNCHANGED <<uplink, sending, asking, preemptsLeft>>))

AskForUplink(d) ==
  ( (buffered[d] > 0)
   /\  (d \notin asking)
   /\  (asking' = asking \cup {d})
   /\  (UNCHANGED <<uplink, sending, buffered, preemptsLeft>>))

GrantUplink(d) ==
  ( (uplink = NoDrone)
   /\  (d \in asking)
   /\  (uplink' = d)
   /\  (asking' = asking \ {d})
   /\  (UNCHANGED <<sending, buffered, preemptsLeft>>))

KeyTransmitter(d) ==
  ( (uplink = d)
   /\  (d \notin sending)
   /\  (buffered[d] > 0)
   /\  (sending' = sending \cup {d})
   /\  (UNCHANGED <<uplink, buffered, asking, preemptsLeft>>))

DrainFrame(d) ==
  ( (d \in sending)
   /\  (buffered[d] > 1)
   /\  (buffered' = [buffered EXCEPT ![d] = @ - 1])
   /\  (UNCHANGED <<uplink, sending, asking, preemptsLeft>>))

StopAndRelease(d) ==
  ( (uplink = d)
   /\  (sending' = sending \ {d})
   /\  (uplink' = NoDrone)
   /\  (UNCHANGED <<buffered, asking, preemptsLeft>>))

CommanderPreempts(d) ==
  ( (preemptsLeft > 0)
   /\  (uplink # NoDrone)
   /\  (uplink # d)
   /\  (uplink' = d)
   /\  (sending' = {})
   /\  (asking' = asking \ {d})
   /\  (preemptsLeft' = preemptsLeft - 1)
   /\  (UNCHANGED buffered))

Next ==
  \E d \in Drones :
    ( (BufferFrame(d) \/ AskForUplink(d) \/ GrantUplink(d))
     \/  (KeyTransmitter(d) \/ DrainFrame(d) \/ StopAndRelease(d))
     \/  (CommanderPreempts(d)))

Spec ==
  ( (Init /\ [][Next]_vars)
   /\  (WF_vars(StopAndRelease(DroneOne)))
   /\  (WF_vars(StopAndRelease(DroneTwo))))

TransmissionsAlwaysEnd ==
  \A d \in Drones : (d \in sending) ~> (d \notin sending)

====