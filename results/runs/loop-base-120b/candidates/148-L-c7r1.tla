---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, NoHash, NoBlock

(*--------------------------------------------------------------------
  Types and helper definitions
--------------------------------------------------------------------*)

BlockType == {"genesis", "send", "open", "receive", "change"}

Block == [type           : BlockType,
          prev           : Hash,
          account        : PublicKey,
          signature      : STRING,
          amount         : Nat,
          recipient      : PublicKey,
          source         : Hash,
          representative : PublicKey]

BlockOrNil == Block \cup {NoBlock}

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)

VARIABLES
    lastHash,            \* the most recent block hash
    ledger,              \* Node -> (Hash -> BlockOrNil)
    received,            \* Node -> SUBSET Hash
    GenesisCreated       \* BOOLEAN flag to guarantee a single genesis block

(*--------------------------------------------------------------------
  Init
--------------------------------------------------------------------*)

Init ==
    /\ lastHash = NoHash
    /\ GenesisCreated = FALSE
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(*--------------------------------------------------------------------
  Abstract mappings (to be supplied in the .cfg)
--------------------------------------------------------------------*)

PrivToPub(p) == CHOOSE pk \in PublicKey : TRUE
NodePriv(n) == CHOOSE k \in PrivateKey : TRUE
NodePub(n) == PrivToPub(NodePriv(n))

(*--------------------------------------------------------------------
  Cryptographic placeholders
--------------------------------------------------------------------*)

ValidSignature(b) ==
    /\ b.signature = "valid"

(*--------------------------------------------------------------------
  Balance (abstract – details omitted)
--------------------------------------------------------------------*)

Balance(pub) ==
    CHOOSE b \in Nat : TRUE

(*--------------------------------------------------------------------
  Hash calculation (abstract implementation)
--------------------------------------------------------------------*)

CalculateHashImpl(prev, data) ==
    CHOOSE h \in Hash : TRUE

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

CreateGenesis ==
    /\ ~GenesisCreated
    /\ LET creatorNode == CHOOSE n \in Node : TRUE
           creatorAcc  == NodePub(creatorNode)
           h == CHOOSE hh \in Hash : hh # NoHash
           b == [type           |-> "genesis",
                prev           |-> NoHash,
                account        |-> creatorAcc,
                signature      |-> "valid",
                amount         |-> GenesisBalance,
                recipient      |-> creatorAcc,
                source         |-> NoHash,
                representative|-> creatorAcc]
       IN
          /\ lastHash' = h
          /\ GenesisCreated' = TRUE
          /\ ledger' = [n \in Node |-> [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n][h2]]]
          /\ received' = [n \in Node |-> {}]
          /\ UNCHANGED <<>>

CreateSend ==
    /\ GenesisCreated
    /\ LET senderNode   == CHOOSE n \in Node : TRUE
           senderAcc    == NodePub(senderNode)
           prevHash     == lastHash
           amount       == CHOOSE a \in Nat : a <= Balance(senderAcc)
           recipientAcc == CHOOSE pk \in PublicKey : pk # senderAcc
           h            == CHOOSE hh \in Hash : hh # NoHash
           b == [type           |-> "send",
                prev           |-> prevHash,
                account        |-> senderAcc,
                signature      |-> "valid",
                amount         |-> amount,
                recipient      |-> recipientAcc,
                source         |-> NoHash,
                representative|-> senderAcc]
       IN
          /\ lastHash' = h
          /\ ledger' = ledger            \* block not yet stored
          /\ received' = [n \in Node |-> received[n] \cup {h}]
          /\ UNCHANGED <<GenesisCreated>>

CreateOpen ==
    /\ GenesisCreated
    /\ LET receiverNode == CHOOSE n \in Node : TRUE
           receiverAcc  == NodePub(receiverNode)
           sourceHash   == CHOOSE sh \in Hash : TRUE
           h            == CHOOSE hh \in Hash : hh # NoHash
           b == [type           |-> "open",
                prev           |-> NoHash,
                account        |-> receiverAcc,
                signature      |-> "valid",
                amount         |-> 0,
                recipient      |-> receiverAcc,
                source         |-> sourceHash,
                representative|-> receiverAcc]
       IN
          /\ lastHash' = h
          /\ ledger' = ledger
          /\ received' = [n \in Node |-> received[n] \cup {h}]
          /\ UNCHANGED <<GenesisCreated>>

CreateReceive ==
    /\ GenesisCreated
    /\ LET receiverNode == CHOOSE n \in Node : TRUE
           receiverAcc  == NodePub(receiverNode)
           prevHash     == lastHash
           sourceHash   == CHOOSE sh \in Hash : TRUE
           h            == CHOOSE hh \in Hash : hh # NoHash
           b == [type           |-> "receive",
                prev           |-> prevHash,
                account        |-> receiverAcc,
                signature      |-> "valid",
                amount         |-> 0,
                recipient      |-> receiverAcc,
                source         |-> sourceHash,
                representative|-> receiverAcc]
       IN
          /\ lastHash' = h
          /\ ledger' = ledger
          /\ received' = [n \in Node |-> received[n] \cup {h}]
          /\ UNCHANGED <<GenesisCreated>>

CreateChange ==
    /\ GenesisCreated
    /\ LET changerNode == CHOOSE n \in Node : TRUE
           changerAcc  == NodePub(changerNode)
           prevHash    == lastHash
           newRep      == CHOOSE pk \in PublicKey : TRUE
           h           == CHOOSE hh \in Hash : hh # NoHash
           b == [type           |-> "change",
                prev           |-> prevHash,
                account        |-> changerAcc,
                signature      |-> "valid",
                amount         |-> 0,
                recipient      |-> changerAcc,
                source         |-> NoHash,
                representative|-> newRep]
       IN
          /\ lastHash' = h
          /\ ledger' = ledger
          /\ received' = [n \in Node |-> received[n] \cup {h}]
          /\ UNCHANGED <<GenesisCreated>>

ProcessBlock ==
    /\ \E n \in Node:
          \E h \in received[n]:
            LET b == CHOOSE blk \in Block : TRUE
            IN
               /\ ValidSignature(b)
               /\ ledger' = [n2 \in Node |-> IF n2 = n
                                           THEN [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n2][h2]]
                                           ELSE ledger[n2]]
               /\ received' = [n2 \in Node |-> IF n2 = n THEN received[n2] \ {h} ELSE received[n2]]
               /\ UNCHANGED <<lastHash, GenesisCreated>>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

Spec == Init /\ [][Next]_<<lastHash, ledger, received, GenesisCreated>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)

TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> BlockOrNil]]
    /\ received \in [Node -> SUBSET Hash]
    /\ GenesisCreated \in BOOLEAN

SafetyInvariant ==
    /\ \A n \in Node:
          \A h \in Hash:
            IF ledger[n][h] # NoBlock
            THEN ValidSignature(ledger[n][h])
            ELSE TRUE

====