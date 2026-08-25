---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

(* shorthands for sentinels *)
NoHash == NoHashVal
NoBlock == NoBlockVal

(* ----------------------------------------------------------------------
   Block definition
   ---------------------------------------------------------------------- *)
Block ==
    [ type    : {"genesis","send","open","receive","change","none"},
      prev    : Hash,
      account : PublicKey,
      amount  : Nat,
      dest    : STRING,
      sig     : STRING ]

VARIABLES
    lastHash, ledger, received

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]

(* ----------------------------------------------------------------------
   Abstract cryptographic primitives (place‑holders)
   ---------------------------------------------------------------------- *)
Sign(sk, data) == <<sk, data>>

ValidSignature(b) == TRUE

(* ----------------------------------------------------------------------
   Hash calculation – to be overridden by the .cfg file
   ---------------------------------------------------------------------- *)
CalculateHashImpl(prev, data) ==
    CHOOSE h \in Hash : h # NoHash

(* ----------------------------------------------------------------------
   Action: create the genesis block (once)
   ---------------------------------------------------------------------- *)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E sk \in PrivateKey :
        LET pk   == sk
            blk  == [ type    |-> "genesis",
                     prev    |-> NoHash,
                     account |-> pk,
                     amount  |-> GenesisBalance,
                     dest    |-> "",
                     sig     |-> Sign(sk, << "genesis", NoHash, pk, GenesisBalance >>) ]
            h    == CalculateHash(NoHash, blk)
        IN
            /\ h # NoHash
            /\ lastHash' = h
            /\ ledger'   = [ n \in Node |-> 
                               [ hh \in Hash |-> IF hh = h THEN blk ELSE ledger[n][hh] ] ]
            /\ received' = received

(* ----------------------------------------------------------------------
   Action: create a send block
   ---------------------------------------------------------------------- *)
CreateSend ==
    /\ lastHash # NoHash
    /\ \E sk \in PrivateKey, amt \in Nat, dst \in STRING :
        LET pk   == sk
            blk  == [ type    |-> "send",
                     prev    |-> lastHash,
                     account |-> pk,
                     amount  |-> amt,
                     dest    |-> dst,
                     sig     |-> Sign(sk, << "send", lastHash, pk, dst, amt >>) ]
            h    == CalculateHash(lastHash, blk)
        IN
            /\ h # NoHash
            /\ lastHash' = h
            /\ ledger'   = [ n \in Node |-> 
                               [ hh \in Hash |-> IF hh = h THEN blk ELSE ledger[n][hh] ] ]
            /\ received' = [ n \in Node |-> received[n] \cup {h} ]

(* ----------------------------------------------------------------------
   Action: create an open block
   ---------------------------------------------------------------------- *)
CreateOpen ==
    /\ lastHash # NoHash
    /\ \E sk \in PrivateKey, srcHash \in Hash :
        LET pk   == sk
            blk  == [ type    |-> "open",
                     prev    |-> NoHash,
                     account |-> pk,
                     amount  |-> 0,
                     dest    |-> srcHash,
                     sig     |-> Sign(sk, << "open", NoHash, pk, srcHash >>) ]
            h    == CalculateHash(NoHash, blk)
        IN
            /\ h # NoHash
            /\ lastHash' = h
            /\ ledger'   = [ n \in Node |-> 
                               [ hh \in Hash |-> IF hh = h THEN blk ELSE ledger[n][hh] ] ]
            /\ received' = [ n \in Node |-> received[n] \cup {h} ]

(* ----------------------------------------------------------------------
   Action: create a receive block
   ---------------------------------------------------------------------- *)
CreateReceive ==
    /\ lastHash # NoHash
    /\ \E sk \in PrivateKey, srcHash \in Hash, amt \in Nat :
        LET pk   == sk
            blk  == [ type    |-> "receive",
                     prev    |-> lastHash,
                     account |-> pk,
                     amount  |-> amt,
                     dest    |-> srcHash,
                     sig     |-> Sign(sk, << "receive", lastHash, pk, srcHash, amt >>) ]
            h    == CalculateHash(lastHash, blk)
        IN
            /\ h # NoHash
            /\ lastHash' = h
            /\ ledger'   = [ n \in Node |-> 
                               [ hh \in Hash |-> IF hh = h THEN blk ELSE ledger[n][hh] ] ]
            /\ received' = [ n \in Node |-> received[n] \cup {h} ]

(* ----------------------------------------------------------------------
   Action: create a change‑representative block
   ---------------------------------------------------------------------- *)
CreateChangeRep ==
    /\ lastHash # NoHash
    /\ \E sk \in PrivateKey, newRep \in STRING :
        LET pk   == sk
            blk  == [ type    |-> "change",
                     prev    |-> lastHash,
                     account |-> pk,
                     amount  |-> 0,
                     dest    |-> newRep,
                     sig     |-> Sign(sk, << "change", lastHash, pk, newRep >>) ]
            h    == CalculateHash(lastHash, blk)
        IN
            /\ h # NoHash
            /\ lastHash' = h
            /\ ledger'   = [ n \in Node |-> 
                               [ hh \in Hash |-> IF hh = h THEN blk ELSE ledger[n][hh] ] ]
            /\ received' = [ n \in Node |-> received[n] \cup {h} ]

(* ----------------------------------------------------------------------
   Action: process a received block on a node
   ---------------------------------------------------------------------- *)
ProcessReceived ==
    /\ \E n \in Node :
        /\ \E h \in received[n] :
            /\ received' = [ m \in Node |-> IF m = n THEN received[m] \ {h} ELSE received[m] ]
            /\ UNCHANGED << lastHash, ledger >>

(* ----------------------------------------------------------------------
   Combined next‑state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChangeRep
    \/ ProcessReceived

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            (ledger[n][h] # NoBlock) => ValidSignature(ledger[n][h])

====