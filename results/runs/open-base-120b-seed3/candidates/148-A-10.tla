---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node,
  GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock,
  PrivToPub, NodePriv

VARIABLES
  lastHash, ledger, received

(*-------------------------------------------------------------------*)
(* Types *)

Block == [type           : {"genesis","send","open","receive","change"},
          prev           : Hash \/ {NoHash},
          account        : PublicKey,
          amount         : Nat,
          recipient      : PublicKey \/ {NoHash},
          representative : PublicKey \/ {NoHash},
          signature      : Nat]   \* abstract signature

BlockOrEmpty == Block \/ {NoBlockVal}

(*-------------------------------------------------------------------*)
(* Helper functions *)

ValidSignature(b) == TRUE   \* abstract – always true for this model

(*-------------------------------------------------------------------*)
(* Initial state *)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

(*-------------------------------------------------------------------*)
(* Actions *)

GenesisCreate ==
  /\ lastHash = NoHashVal
  /\ \E pub \in PublicKey :
        LET blk ==
              [type           |-> "genesis",
               prev           |-> NoHash,
               account        |-> pub,
               amount         |-> GenesisBalance,
               recipient      |-> NoHash,
               representative |-> NoHash,
               signature      |-> 0]
        IN
        LET h == CalculateHash(blk, NoHash) IN
        /\ lastHash' = h
        /\ ledger'   = [n \in Node |-> [h2 \in Hash |-> IF h2 = h THEN blk ELSE NoBlockVal]]
        /\ received' = [n \in Node |-> {}]
        /\ UNCHANGED << >>

SendCreate ==
  /\ \E senderPub \in PublicKey :
        \E amt \in Nat :
          amt > 0 /\ amt <= GenesisBalance   \* (simplified balance check)
        /\ \E recPub \in PublicKey :
            LET blk ==
                  [type           |-> "send",
                   prev           |-> lastHash,
                   account        |-> senderPub,
                   amount         |-> amt,
                   recipient      |-> recPub,
                   representative |-> NoHash,
                   signature      |-> 0]
            IN
            LET h == CalculateHash(blk, lastHash) IN
            /\ lastHash' = h
            /\ ledger'   = ledger
            /\ received' = [n \in Node |-> received[n] \cup {h}]
            /\ UNCHANGED << >>

OpenCreate ==
  /\ \E newPub \in PublicKey :
        \E srcHash \in Hash :
          /\ ledger[Node][srcHash] # NoBlockVal
          /\ ledger[Node][srcHash].type = "send"
          /\ ledger[Node][srcHash].recipient = newPub
        LET blk ==
              [type           |-> "open",
               prev           |-> NoHash,
               account        |-> newPub,
               amount         |-> ledger[Node][srcHash].amount,
               recipient      |-> NoHash,
               representative |-> NoHash,
               signature      |-> 0]
        IN
        LET h == CalculateHash(blk, NoHash) IN
        /\ lastHash' = h
        /\ ledger'   = ledger
        /\ received' = [n \in Node |-> received[n] \cup {h}]
        /\ UNCHANGED << >>

ReceiveCreate ==
  /\ \E recPub \in PublicKey :
        \E srcHash \in Hash :
          /\ ledger[Node][srcHash].type = "send"
          /\ ledger[Node][srcHash].recipient = recPub
        LET blk ==
              [type           |-> "receive",
               prev           |-> lastHash,
               account        |-> recPub,
               amount         |-> ledger[Node][srcHash].amount,
               recipient      |-> NoHash,
               representative |-> NoHash,
               signature      |-> 0]
        IN
        LET h == CalculateHash(blk, lastHash) IN
        /\ lastHash' = h
        /\ ledger'   = ledger
        /\ received' = [n \in Node |-> received[n] \cup {h}]
        /\ UNCHANGED << >>

ChangeRepCreate ==
  /\ \E acctPub \in PublicKey :
        \E newRep \in PublicKey :
            LET blk ==
                  [type           |-> "change",
                   prev           |-> lastHash,
                   account        |-> acctPub,
                   amount         |-> 0,
                   recipient      |-> NoHash,
                   representative |-> newRep,
                   signature      |-> 0]
            IN
            LET h == CalculateHash(blk, lastHash) IN
            /\ lastHash' = h
            /\ ledger'   = ledger
            /\ received' = [n \in Node |-> received[n] \cup {h}]
            /\ UNCHANGED << >>

ProcessReceived ==
  /\ \E n \in Node :
        \E h \in received[n] :
            /\ ledger'   = ledger
            /\ received' = [m \in Node |-> IF m = n THEN received[m] \ {h} ELSE received[m]]
            /\ UNCHANGED lastHash

Next ==
  \/ GenesisCreate
  \/ SendCreate
  \/ OpenCreate
  \/ ReceiveCreate
  \/ ChangeRepCreate
  \/ ProcessReceived

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(*-------------------------------------------------------------------*)
(* Invariants *)

TypeInvariant ==
  /\ lastHash \in Hash \/ {NoHashVal}
  /\ ledger   \in [Node -> [Hash -> BlockOrEmpty]]
  /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
  \A n \in Node :
    \A h \in Hash :
      IF ledger[n][h] # NoBlockVal
      THEN ValidSignature(ledger[n][h])
      ELSE TRUE

(*-------------------------------------------------------------------*)
(* Concrete hash implementation for model checking *)

CalculateHashImpl(b, prev) ==
  (* pick an arbitrary hash from the finite set *)
  CHOOSE h \in Hash : TRUE

====