---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Constants (named exactly as required)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Hash,            \* Set of all possible block hashes
    NoHashVal,       \* Sentinel value meaning “no hash yet”
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total amount of coins in the system
    NoBlockVal,      \* Sentinel meaning “no block”
    CalculateHash,   \* Abstract hash function
    NoHash,          \* Alias for NoHashVal (used in the config)
    NoBlock          \* Alias for NoBlockVal (used in the config)

(* ----------------------------------------------------------------------
   Types for readability
   ---------------------------------------------------------------------- *)
BlockType == {"genesis", "send", "open", "receive", "change"}

Block ==
    [ type          : BlockType,
      hash          : Hash,
      prev          : {NoHash} \cup Hash,
      account       : PublicKey,          \* owner of the chain
      amount        : Nat,
      recipient     : PublicKey,
      source        : Hash,
      representative: PublicKey,
      signature     : STRING ]   \* abstract representation

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES
    lastHash,        \* The most recent block hash seen by the system
    ledgers,         \* Function: Node -> [Hash -> Block \cup {NoBlock}]
    received         \* Function: Node -> SUBSET Hash (blocks waiting validation)

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

\* The public key belonging to a private key (abstract mapping)
PublicKeyOf == [pk \in PrivateKey |-> CHOOSE pk2 \in PublicKey :
                                    TRUE]   \* nondeterministic but total

\* An abstract signature function (a pure function of the private key and block content)
Sign == [pk \in PrivateKey, b \in Block |-> "sig_" \o ToString(pk) \o "_" \o ToString(b.hash)]

\* Check whether a block's signature matches the expected signature for its account's private key
SigOK(b) ==
    LET ownerPriv == CHOOSE p \in PrivateKey : PublicKeyOf[p] = b.account IN
    b.signature = Sign[ownerPriv, b]

\* Balance of an account on a particular node (recursive walk of the chain)
Balance(node, acc) ==
    LET chain == [h \in ledgers[node] : h.account = acc] IN
    \E h \in chain :
        IF h.type = "receive" THEN
            Balance(node, h.account) + h.amount
        ELSE IF h.type = "send" THEN
            Balance(node, h.account) - h.amount
        ELSE IF h.type = "open" THEN
            h.amount
        ELSE IF h.type = "genesis" THEN
            GenesisBalance
        ELSE IF h.type = "change" THEN
            Balance(node, h.account)
        ELSE 0

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ lastHash = NoHashVal
    /\ ledgers = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

CreateGenesis ==
    \E pk \in PrivateKey :
        LET acc == PublicKeyOf[pk] IN
        LET b ==
            [ type          |-> "genesis",
              hash          |-> CalculateHash[<<>>, NoHashVal],
              prev          |-> NoHashVal,
              account       |-> acc,
              amount        |-> GenesisBalance,
              recipient     |-> acc,
              source        |-> NoHashVal,
              representative|-> acc,
              signature     |-> Sign[pk, @] ] IN
        /\ lastHash = NoHashVal
        /\ lastHash' = b.hash
        /\ \A n \in Node :
            /\ ledgers' = [ledgers EXCEPT ![n][b.hash] = b]
            /\ received' = [received EXCEPT ![n] = {}]
        /\ UNCHANGED <<>>   \* all other variables unchanged

CreateSend ==
    \E n \in Node, pk \in PrivateKey, rec \in PublicKey :
        LET senderAcc == PublicKeyOf[pk] IN
        LET prevHash == lastHash IN
        LET amount == 1 \* (for simplicity, fixed amount) IN
        /\ Balance(n, senderAcc) >= amount
        LET b ==
            [ type          |-> "send",
              hash          |-> CalculateHash[<<senderAcc, amount, rec>>, prevHash],
              prev          |-> prevHash,
              account       |-> senderAcc,
              amount        |-> amount,
              recipient     |-> rec,
              source        |-> NoHashVal,
              representative|-> senderAcc,
              signature     |-> Sign[pk, @] ] IN
        /\ lastHash' = b.hash
        /\ \A m \in Node :
            /\ ledgers' = [ledgers EXCEPT ![m][b.hash] = NoBlockVal]
            /\ received' = [received EXCEPT ![m] = @ \cup {b.hash}]
        /\ UNCHANGED <<>>

CreateReceive ==
    \E n \in Node, pk \in PrivateKey, srcHash \in Hash :
        LET acc == PublicKeyOf[pk] IN
        LET recBlock == ledgers[n][srcHash] IN
        /\ recBlock.type = "send"
        /\ recBlock.recipient = acc
        /\ \E prevHash \in ledgers[n] :
            LET b ==
                [ type          |-> "receive",
                  hash          |-> CalculateHash[<<srcHash>>, prevHash],
                  prev          |-> prevHash,
                  account       |-> acc,
                  amount        |-> 0,
                  recipient     |-> acc,
                  source        |-> srcHash,
                  representative|-> acc,
                  signature     |-> Sign[pk, @] ] IN
            /\ lastHash' = b.hash
            /\ ledgers' = [ledgers EXCEPT ![n][b.hash] = b]
            /\ received' = [received EXCEPT ![n] = @ \ {srcHash}]
            /\ UNCHANGED <<>>

CreateOpen ==
    \E n \in Node, pk \in PrivateKey, srcHash \in Hash :
        LET acc == PublicKeyOf[pk] IN
        LET srcBlock == ledgers[n][srcHash] IN
        /\ srcBlock.type = "send"
        /\ srcBlock.recipient = acc
        /\ \E b \in ledgers[n] :
            b.type = "receive" /\ b.source = srcHash
            => FALSE   \* cannot open if already received
        LET openBlock ==
            [ type          |-> "open",
              hash          |-> CalculateHash[<<srcHash>>, NoHashVal],
              prev          |-> NoHashVal,
              account       |-> acc,
              amount        |-> srcBlock.amount,
              recipient     |-> acc,
              source        |-> srcHash,
              representative|-> acc,
              signature     |-> Sign[pk, @] ] IN
        /\ lastHash' = openBlock.hash
        /\ ledgers' = [ledgers EXCEPT ![n][openBlock.hash] = openBlock]
        /\ received' = [received EXCEPT ![n] = @ \ {srcHash}]
        /\ UNCHANGED <<>>

CreateChangeRep ==
    \E n \in Node, pk \in PrivateKey, newRep \in PublicKey :
        LET acc == PublicKeyOf[pk] IN
        LET prevHash == lastHash IN
        LET b ==
            [ type          |-> "change",
              hash          |-> CalculateHash[<<newRep>>, prevHash],
              prev          |-> prevHash,
              account       |-> acc,
              amount        |-> 0,
              recipient     |-> acc,
              source        |-> NoHashVal,
              representative|-> newRep,
              signature     |-> Sign[pk, @] ] IN
        /\ lastHash' = b.hash
        /\ \A m \in Node :
            /\ ledgers' = [ledgers EXCEPT ![m][b.hash] = b]
            /\ received' = [received EXCEPT ![m] = {}]
        /\ UNCHANGED <<>>

ProcessReceived ==
    \E n \in Node, h \in received[n] :
        LET b == ledgers[n][h] IN
        /\ b # NoBlockVal
        /\ SigOK(b)
        /\ CASE b.type = "send" -> /\ b.amount <= Balance(n, b.account)
                     b.type = "receive" -> /\ b.source # NoHashVal
                                            /\ \E src \in ledgers[n] : src.hash = b.source /\ src.type = "send"
                     b.type = "open" -> /\ b.source # NoHashVal
                                         /\ \E src \in ledgers[n] : src.hash = b.source /\ src.type = "send"
                     b.type = "change" -> TRUE
                     b.type = "genesis" -> TRUE
                     OTHER -> FALSE
        /\ ledgers' = [ledgers EXCEPT ![n][h] = b]
        /\ received' = [received EXCEPT ![n] = @ \ {h}]
        /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChangeRep
    \/ ProcessReceived

(* ----------------------------------------------------------------------
   Safety invariant (the cryptographic invariant)
   ---------------------------------------------------------------------- *)
SafetyInvariant ==
    \A n \in Node, h \in Hash :
        LET b == ledgers[n][h] IN
        b = NoBlockVal \/ SigOK(b)

(* ----------------------------------------------------------------------
   Type invariant – ensures variables stay within declared domains
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ lastHash \in {NoHashVal} \cup Hash
    /\ ledgers \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<lastHash, ledgers, received>>

====