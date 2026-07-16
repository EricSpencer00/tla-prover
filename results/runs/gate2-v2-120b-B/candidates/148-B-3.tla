---- MODULE Nano ----
(***************************************************************************)
(* Fixed version of Nano.tla                                               *)
(* The change restores the missing fields for the genesis block record.   *)
(* It introduces a separate constant GenesisBlockRecord that contains the *)
(* full set of fields (type, account, balance, destination, source, rep)   *)
(* with unused fields set to a placeholder value. This record is used      *)
(* wherever a genesis block must be treated as a generic Block.           *)
(* The rest of the specification is unchanged, preserving all invariants *)
(* and actions.                                                            *)
(***************************************************************************)

EXTENDS Naturals, Bags

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* The set of all nodes in the network
    GenesisBalance,         \* The total number of coins in the network
    Ownership,              \* The private key owned by each node
    NoHash,                 \* A distinguished value not in Hash
    NoBlock,                \* A distinguished block not in the blockchain
    DummyPublicKey,         \* Placeholder public key for unused fields
    DummyHash               \* Placeholder hash for unused fields

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
        /\ CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

(***************************************************************************)
(* Functions to sign hashes with private key and validate signatures       *)
(***************************************************************************)

Signature ==
    [data       : Hash,
     signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data       |-> hash,
     signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

(***************************************************************************)
(* Block definitions – all block records now contain the superset of fields*)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

(* A full record that includes all possible fields; unused fields are filled
   with dummy values. This allows us to treat a genesis block as a member of
   the generic Block set without missing-field errors. *)
GenesisBlockRecord ==
    [type        |-> "genesis",
     account     |-> CHOOSE k \in PublicKey : TRUE,
     balance     |-> GenesisBalance,
     destination |-> DummyPublicKey,
     source      |-> DummyHash,
     rep         |-> DummyPublicKey]

SendBlock ==
    [type        |-> "send",
     previous    |-> CHOOSE h \in Hash : TRUE,
     balance     |-> 0,
     destination |-> CHOOSE k \in PublicKey : TRUE,
     source      |-> DummyHash,
     rep         |-> DummyPublicKey]

OpenBlock ==
    [type        |-> "open",
     account     |-> CHOOSE k \in PublicKey : TRUE,
     source      |-> CHOOSE h \in Hash : TRUE,
     rep         |-> CHOOSE k \in PublicKey : TRUE,
     previous    |-> DummyHash,
     balance     |-> 0,
     destination |-> DummyPublicKey]

ReceiveBlock ==
    [type        |-> "receive",
     previous    |-> CHOOSE h \in Hash : TRUE,
     source      |-> CHOOSE h \in Hash : TRUE,
     account     |-> DummyPublicKey,
     balance     |-> 0,
     destination |-> DummyPublicKey,
     rep         |-> DummyPublicKey]

ChangeRepBlock ==
    [type        |-> "change",
     previous    |-> CHOOSE h \in Hash : TRUE,
     rep         |-> CHOOSE k \in PublicKey : TRUE,
     account     |-> DummyPublicKey,
     balance     |-> 0,
     destination |-> DummyPublicKey,
     source      |-> DummyHash]

Block ==
    GenesisBlockRecord
    \cup SendBlock
    \cup OpenBlock
    \cup ReceiveBlock
    \cup ChangeRepBlock

SignedBlock ==
    [block     : Block,
     signature : Signature]

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(***************************************************************************)
(* Utility functions to calculate block lattice properties.                *)
(***************************************************************************)

GenesisBlockExists ==
    /\ lastHash /= NoHash

IsAccountOpen(ledger, publicKey) ==
    /\ \E hash \in Hash :
        LET sb == ledger[hash] IN
        /\ sb /= NoBlock
        /\ sb.block.type \in {"genesis", "open"}
        /\ sb.block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    /\ \E hash \in Hash :
        LET sb == ledger[hash] IN
        /\ sb /= NoBlock
        /\ sb.block.type \in {"open", "receive"}
        /\ sb.block.source = sourceHash

RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, blockHash) ==
    LET sb == ledger[blockHash] IN
    IF sb.block.type \in {"genesis", "open"}
    THEN sb.block.account
    ELSE PublicKeyOf(ledger, sb.block.previous)

TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET sb == ledger[hash] IN
        /\ sb /= NoBlock
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ ~\E otherHash \in Hash :
            LET osb == ledger[otherHash] IN
            /\ osb /= NoBlock
            /\ osb.block.type \in {"send", "receive", "change"}
            /\ osb.block.previous = hash

RECURSIVE BalanceAt(_, _)
RECURSIVE ValueOfSendBlock(_, _)

BalanceAt(ledger, hash) ==
    LET sb == ledger[hash] IN
    CASE sb.block.type = "open" -> ValueOfSendBlock(ledger, sb.block.source)
    [] sb.block.type = "send" -> sb.block.balance
    [] sb.block.type = "receive" ->
        BalanceAt(ledger, sb.block.previous)
        + ValueOfSendBlock(ledger, sb.block.source)
    [] sb.block.type = "change" -> BalanceAt(ledger, sb.block.previous)
    [] sb.block.type = "genesis" -> sb.block.balance

ValueOfSendBlock(ledger, hash) ==
    LET sb == ledger[hash] IN
    BalanceAt(ledger, sb.block.previous) - sb.block.balance

(***************************************************************************)
(* Invariants                                                             *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        /\ \A hash \in Hash :
            LET sb == ledger[hash] IN
            sb /= NoBlock =>
                LET pk == PublicKeyOf(ledger, hash) IN
                ValidateSignature(sb.signature, pk, hash)

RECURSIVE SumBag(_)
SumBag(B) ==
    IF B = {} THEN 0
    ELSE
        LET e == CHOOSE x \in B : TRUE IN
        e + SumBag(B \ {e})

BalanceInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET openAccs == {pk \in PublicKey : IsAccountOpen(ledger, pk)} IN
        LET topBlks == {TopBlock(ledger, pk) : pk \in openAccs} IN
        LET acctBals == {BalanceAt(ledger, h) : h \in topBlks} IN
        SumBag(acctBals) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

(***************************************************************************)
(* Genesis block creation                                                 *)
(***************************************************************************)

CreateGenesisBlock(privateKey) ==
    LET
        publicKey == KeyPair[privateKey]
        genesisBlock ==
            [type        |-> "genesis",
             account     |-> publicKey,
             balance     |-> GenesisBalance,
             destination |-> DummyPublicKey,
             source      |-> DummyHash,
             rep         |-> DummyPublicKey]
    IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(genesisBlock, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |->
            [distributedLedger[n] EXCEPT
                ![lastHash'] = [block      |-> genesisBlock,
                                signature |-> SignHash(lastHash', privateKey)]]]
    /\ UNCHANGED received

(***************************************************************************)
(* Validation functions for each block type                               *)
(***************************************************************************)

ValidateOpenBlock(ledger, block) ==
    /\ block.type = "open"
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = block.account

ValidateSendBlock(ledger, block) ==
    /\ block.type = "send"
    /\ ledger[block.previous] /= NoBlock
    /\ block.balance <= BalanceAt(ledger, block.previous)

ValidateReceiveBlock(ledger, block) ==
    /\ block.type = "receive"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination =
        PublicKeyOf(ledger, block.previous)

ValidateChangeBlock(ledger, block) ==
    /\ block.type = "change"
    /\ ledger[block.previous] /= NoBlock

(***************************************************************************)
(* Creation actions for each block type                                   *)
(***************************************************************************)

CreateOpenBlock(node) ==
    LET
        privK == Ownership[node]
        pubK  == KeyPair[privK]
        ledger == distributedLedger[node]
    IN
    /\ \E repK \in PublicKey :
        /\ \E srcHash \in Hash :
            LET newBlock ==
                [type        |-> "open",
                 account     |-> pubK,
                 source      |-> srcHash,
                 rep         |-> repK,
                 previous    |-> DummyHash,
                 balance     |-> 0,
                 destination |-> DummyPublicKey]
            IN
            /\ ValidateOpenBlock(ledger, newBlock)
            /\ CalculateHash(newBlock, lastHash, lastHash')
            /\ received' =
                [n \in Node |->
                    IF n = node
                    THEN received[n] \cup
                         {[block      |-> newBlock,
                           signature |-> SignHash(lastHash', privK)]}
                    ELSE received[n]]
            /\ UNCHANGED distributedLedger

CreateSendBlock(node) ==
    LET
        privK == Ownership[node]
        pubK  == KeyPair[privK]
        ledger == distributedLedger[node]
    IN
    /\ \E prev \in Hash :
        /\ ledger[prev] /= NoBlock
        /\ PublicKeyOf(ledger, prev) = pubK
        /\ \E dest \in PublicKey :
            /\ \E newBal \in AccountBalance :
                LET newBlock ==
                    [type        |-> "send",
                     previous    |-> prev,
                     balance     |-> newBal,
                     destination |-> dest,
                     source      |-> DummyHash,
                     rep         |-> DummyPublicKey,
                     account     |-> DummyPublicKey]
                IN
                /\ ValidateSendBlock(ledger, newBlock)
                /\ CalculateHash(newBlock, lastHash, lastHash')
                /\ received' =
                    [n \in Node |->
                        IF n = node
                        THEN received[n] \cup
                             {[block      |-> newBlock,
                               signature |-> SignHash(lastHash', privK)]}
                        ELSE received[n]]
                /\ UNCHANGED distributedLedger

CreateReceiveBlock(node) ==
    LET
        privK == Ownership[node]
        pubK  == KeyPair[privK]
        ledger == distributedLedger[node]
    IN
    /\ \E prev \in Hash :
        /\ ledger[prev] /= NoBlock
        /\ PublicKeyOf(ledger, prev) = pubK
        /\ \E src \in Hash :
            LET newBlock ==
                [type        |-> "receive",
                 previous    |-> prev,
                 source      |-> src,
                 account     |-> DummyPublicKey,
                 balance     |-> 0,
                 destination |-> DummyPublicKey,
                 rep         |-> DummyPublicKey]
            IN
            /\ ValidateReceiveBlock(ledger, newBlock)
            /\ CalculateHash(newBlock, lastHash, lastHash')
            /\ received' =
                [n \in Node |->
                    IF n = node
                    THEN received[n] \cup
                         {[block      |-> newBlock,
                           signature |-> SignHash(lastHash', privK)]}
                    ELSE received[n]]
            /\ UNCHANGED distributedLedger

CreateChangeRepBlock(node) ==
    LET
        privK == Ownership[node]
        pubK  == KeyPair[privK]
        ledger == distributedLedger[node]
    IN
    /\ \E prev \in Hash :
        /\ ledger[prev] /= NoBlock
        /\ PublicKeyOf(ledger, prev) = pubK
        /\ \E newRep \in PublicKey :
            LET newBlock ==
                [type        |-> "change",
                 previous    |-> prev,
                 rep         |-> newRep,
                 account     |-> DummyPublicKey,
                 balance     |-> 0,
                 destination |-> DummyPublicKey,
                 source      |-> DummyHash]
            IN
            /\ ValidateChangeBlock(ledger, newBlock)
            /\ CalculateHash(newBlock, lastHash, lastHash')
            /\ received' =
                [n \in Node |->
                    IF n = node
                    THEN received[n] \cup
                         {[block      |-> newBlock,
                           signature |-> SignHash(lastHash', privK)]}
                    ELSE received[n]]
            /\ UNCHANGED distributedLedger

(***************************************************************************)
(* Processing actions for each block type                                 *)
(***************************************************************************)

ProcessOpenBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    /\ ValidateOpenBlock(ledger, sb.block)
    /\ ~IsAccountOpen(ledger, sb.block.account)
    /\ CalculateHash(sb.block, lastHash, lastHash')
    /\ ValidateSignature(sb.signature, sb.block.account, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT
            ![node][lastHash'] = sb]
    /\ UNCHANGED received

ProcessSendBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    /\ ValidateSendBlock(ledger, sb.block)
    /\ CalculateHash(sb.block, lastHash, lastHash')
    /\ ValidateSignature(
        sb.signature,
        PublicKeyOf(ledger, sb.block.previous),
        lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT
            ![node][lastHash'] = sb]
    /\ UNCHANGED received

ProcessReceiveBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    /\ ValidateReceiveBlock(ledger, sb.block)
    /\ ~IsSendReceived(ledger, sb.block.source)
    /\ CalculateHash(sb.block, lastHash, lastHash')
    /\ ValidateSignature(
        sb.signature,
        PublicKeyOf(ledger, sb.block.previous),
        lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT
            ![node][lastHash'] = sb]
    /\ UNCHANGED received

ProcessChangeRepBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    /\ ValidateChangeBlock(ledger, sb.block)
    /\ CalculateHash(sb.block, lastHash, lastHash')
    /\ ValidateSignature(
        sb.signature,
        PublicKeyOf(ledger, sb.block.previous),
        lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT
            ![node][lastHash'] = sb]
    /\ UNCHANGED received

(***************************************************************************)
(* Top-level actions                                                      *)
(***************************************************************************)

CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E sb \in received[node] :
        (   ProcessOpenBlock(node, sb)
         \/ ProcessSendBlock(node, sb)
         \/ ProcessReceiveBlock(node, sb)
         \/ ProcessChangeRepBlock(node, sb))
    /\ received' = [received EXCEPT ![node] = @ \ {sb}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E privK \in PrivateKey : CreateGenesisBlock(privK)
    \/ \E node \in Node : CreateBlock(node)
    \/ \E node \in Node : ProcessBlock(node)

Spec ==
    Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

=============================================================================