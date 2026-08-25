---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, NoHash, NoBlock, ledger, GenesisCreated

(*--------------------------------------------------------------------
  Concrete definitions for sentinel constants
--------------------------------------------------------------------*)

(* A concrete (but arbitrary) hash value to represent the absence of a hash *)
NoHash == CHOOSE h \in Hash : TRUE

(* A concrete (but arbitrary) block value to represent the absence of a block *)
NoBlock == [ type           |-> "genesis",
             prev           |-> NoHash,
             account        |-> CHOOSE pk \in PublicKey : TRUE,
             signature      |-> "invalid",
             amount         |-> 0,
             recipient      |-> CHOOSE pk \in PublicKey : TRUE,
             source         |-> NoHash,
             representative |-> CHOOSE pk \in PublicKey : TRUE ]

(* A concrete (but arbitrary) initial ledger constant (used only to satisfy
   the .cfg substitution; the actual mutable ledger is the variable
   ledgerVar defined below) *)
ledger == [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]

(*--------------------------------------------------------------------
  Types and helper definitions
--------------------------------------------------------------------*)

BlockType == {"genesis", "send", "open", "receive", "change"}

Block == [ type           : BlockType,
           prev           : Hash,
           account        : PublicKey,
           signature      : STRING,
           amount         : Nat,
           recipient      : PublicKey,
           source         : Hash,
           representative : PublicKey ]

BlockOrNil == Block \cup { NoBlock }

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)

VARIABLES
    lastHash,            \* the most recent block hash
    ledgerVar,          \* Node -> (Hash -> BlockOrNil)
    received,           \* Node -> SUBSET Hash
    genesisCreated      \* BOOLEAN flag to guarantee a single genesis block

(*--------------------------------------------------------------------
  Init
--------------------------------------------------------------------*)

Init ==
    /\ lastHash = NoHash
    /\ genesisCreated = FALSE
    /\ ledgerVar = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]

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

(* The identifier required by the .cfg; it will be overridden by
   CalculateHashImpl *)
CalculateHash(prev, data) == CalculateHashImpl(prev, data)

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

CreateGenesis ==
    /\ ~genesisCreated
    /\ LET creatorNode == CHOOSE n \in Node : TRUE
           creatorAcc  == NodePub(creatorNode)
           h == CHOOSE hh \in Hash : hh # NoHash
           b == [ type           |-> "genesis",
                 prev           |-> NoHash,
                 account        |-> creatorAcc,
                 signature      |-> "valid",
                 amount         |-> GenesisBalance,
                 recipient      |-> creatorAcc,
                 source         |-> NoHash,
                 representative|-> creatorAcc ]
       IN
          /\ lastHash' = h
          /\ genesisCreated' = TRUE
          /\ ledgerVar' = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN b ELSE ledgerVar[n][h2] ] ]
          /\ received' = [ n \in Node |-> {} ]
          /\ UNCHANGED <<>>

CreateSend ==
    /\ genesisCreated
    /\ LET senderNode   == CHOOSE n \in Node : TRUE
           senderAcc    == NodePub(senderNode)
           prevHash     == lastHash
           amount       == CHOOSE a \in Nat : a <= Balance(senderAcc)
           recipientAcc == CHOOSE pk \in PublicKey : pk # senderAcc
           h            == CHOOSE hh \in Hash : hh # NoHash
           b == [ type           |-> "send",
                 prev           |-> prevHash,
                 account        |-> senderAcc,
                 signature      |-> "valid",
                 amount         |-> amount,
                 recipient      |-> recipientAcc,
                 source         |-> NoHash,
                 representative|-> senderAcc ]
       IN
          /\ lastHash' = h
          /\ ledgerVar' = ledgerVar            \* block not yet stored
          /\ received' = [ n \in Node |-> received[n] \cup { h } ]
          /\ UNCHANGED <<genesisCreated>>

CreateOpen ==
    /\ genesisCreated
    /\ LET receiverNode == CHOOSE n \in Node : TRUE
           receiverAcc  == NodePub(receiverNode)
           sourceHash   == CHOOSE sh \in Hash : TRUE
           h            == CHOOSE hh \in Hash : hh # NoHash
           b == [ type           |-> "open",
                 prev           |-> NoHash,
                 account        |-> receiverAcc,
                 signature      |-> "valid",
                 amount         |-> 0,
                 recipient      |-> receiverAcc,
                 source         |-> sourceHash,
                 representative|-> receiverAcc ]
       IN
          /\ lastHash' = h
          /\ ledgerVar' = ledgerVar
          /\ received' = [ n \in Node |-> received[n] \cup { h } ]
          /\ UNCHANGED <<genesisCreated>>

CreateReceive ==
    /\ genesisCreated
    /\ LET receiverNode == CHOOSE n \in Node : TRUE
           receiverAcc  == NodePub(receiverNode)
           prevHash     == lastHash
           sourceHash   == CHOOSE sh \in Hash : TRUE
           h            == CHOOSE hh \in Hash : hh # NoHash
           b == [ type           |-> "receive",
                 prev           |-> prevHash,
                 account        |-> receiverAcc,
                 signature      |-> "valid",
                 amount         |-> 0,
                 recipient      |-> receiverAcc,
                 source         |-> sourceHash,
                 representative|-> receiverAcc ]
       IN
          /\ lastHash' = h
          /\ ledgerVar' = ledgerVar
          /\ received' = [ n \in Node |-> received[n] \cup { h } ]
          /\ UNCHANGED <<genesisCreated>>

CreateChange ==
    /\ genesisCreated
    /\ LET changerNode == CHOOSE n \in Node : TRUE
           changerAcc  == NodePub(changerNode)
           prevHash    == lastHash
           newRep      == CHOOSE pk \in PublicKey : TRUE
           h           == CHOOSE hh \in Hash : hh # NoHash
           b == [ type           |-> "change",
                 prev           |-> prevHash,
                 account        |-> changerAcc,
                 signature      |-> "valid",
                 amount         |-> 0,
                 recipient      |-> changerAcc,
                 source         |-> NoHash,
                 representative|-> newRep ]
       IN
          /\ lastHash' = h
          /\ ledgerVar' = ledgerVar
          /\ received' = [ n \in Node |-> received[n] \cup { h } ]
          /\ UNCHANGED <<genesisCreated>>

ProcessBlock ==
    /\ \E n \in Node :
          \E h \in received[n] :
            LET b == CHOOSE blk \in Block : TRUE
            IN
               /\ ValidSignature(b)
               /\ ledgerVar' = [ n2 \in Node |
                                 IF n2 = n
                                 THEN [ h2 \in Hash |
                                         IF h2 = h
                                         THEN b
                                         ELSE ledgerVar[n2][h2] ]
                                 ELSE ledgerVar[n2] ]
               /\ received' = [ n2 \in Node |
                                 IF n2 = n
                                 THEN received[n2] \ { h }
                                 ELSE received[n2] ]
               /\ UNCHANGED <<lastHash, genesisCreated>>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

Spec == Init /\ [][Next]_<<lastHash, ledgerVar, received, genesisCreated>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)

TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledgerVar \in [ Node -> [ Hash -> BlockOrNil ] ]
    /\ received \in [ Node -> SUBSET Hash ]
    /\ genesisCreated \in BOOLEAN

SafetyInvariant ==
    /\ \A n \in Node :
          \A h \in Hash :
            IF ledgerVar[n][h] # NoBlock
            THEN ValidSignature(ledgerVar[n][h])
            ELSE TRUE

====