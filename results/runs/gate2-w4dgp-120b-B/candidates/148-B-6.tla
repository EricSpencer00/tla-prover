---- MODULE Nano ----
(***************************************************************************)
(* An outdated and not-ultimately-useful specification of the original     *)
(* protocol used by the Nano blockchain. Primarily interesting as an       *)
(* example of how to model hash functions and cryptographic signatures,    *)
(* and the difficulties in using finite modelchecking to analyze           *)
(* blockchain-like data structures or anything else that records action    *)
(* history in an ordered way.                                              *)
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
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

(***************************************************************************)
(* Functions to sign hashes with private key and validate signatures       *)
(* against public key.                                                     *)
(***************************************************************************)

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature ==
    [data : Hash, signedWith : PrivateKey]

(***************************************************************************)
(* Defines the set of protocol-conforming blocks.                          *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type |-> "genesis", account |-> CHOOSE pub \in PublicKey : TRUE,
     balance |-> GenesisBalance]

SendBlock ==
    [previous : Hash, balance : AccountBalance, destination : PublicKey, type |-> "send"]

OpenBlock ==
    [account : PublicKey, source : Hash, rep : PublicKey, type |-> "open"]

ReceiveBlock ==
    [previous : Hash, source : Hash, type |-> "receive"]

ChangeRepBlock ==
    [previous : Hash, rep : PublicKey, type |-> "change"]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock ==
    [block : Block, signature : Signature]

NoBlock == CHOOSE b \notin SignedBlock

NoHash == CHOOSE h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(***************************************************************************)
(* Utility functions to calculate block lattice properties.                *)
(***************************************************************************)

GenesisBlockExists == lastHash /= NoHash

IsAccountOpen(ledger, publicKey) ==
    /\ \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ signedBlock.block.type \in {"genesis", "open"}
        /\ signedBlock.block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    /\ \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ signedBlock.block.type \in {"open", "receive"}
        /\ signedBlock.block.source = sourceHash

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, blockHash) ==
    LET signedBlock == ledger[blockHash]
        block == signedBlock.block
    IN IF block.type \in {"genesis", "open"}
       THEN block.account
       ELSE PublicKeyOf(ledger, block.previous)

TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET sb == ledger[hash] IN
        /\ sb /= NoBlock
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ ~\E otherHash \in Hash :
            LET sb2 == ledger[otherHash] IN
            /\ sb2.block.type \in {"send", "receive", "change"}
            /\ sb2.block.previous = hash

RECURSIVE BalanceAt(_, _)
RECURSIVE ValueOfSendBlock(_, _)
BalanceAt(ledger, hash) ==
    LET sb == ledger[hash] IN
    LET block == sb.block IN
    CASE block.type = "open" -> ValueOfSendBlock(ledger, block.source)
      [] block.type = "send" -> block.balance
      [] block.type = "receive" ->
           BalanceAt(ledger, block.previous) + ValueOfSendBlock(ledger, block.source)
      [] block.type = "change" -> BalanceAt(ledger, block.previous)
      [] block.type = "genesis" -> block.balance

ValueOfSendBlock(ledger, hash) ==
    LET sb == ledger[hash] IN
    LET block == sb.block IN
    BalanceAt(ledger, block.previous) - block.balance

(***************************************************************************)
(* The type & safety invariants.                                           *)
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
                   LET pubKey == PublicKeyOf(ledger, hash) IN
                   ValidateSignature(sb.signature, pubKey, hash)

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE LET e == CHOOSE x \in S : TRUE IN e + SumBag(B (-) SetToBag({e}))

BalanceInvariant ==
    /\ \A node \in Node :
         LET ledger == distributedLedger[node]
             openAccounts == {acc \in PublicKey : IsAccountOpen(ledger, acc)}
             topBlocks == {TopBlock(ledger, acc) : acc \in openAccounts}
         IN LET balOf(h) == BalanceAt(ledger, h) IN
            /\ GenesisBlockExists =>
                 /\ SumBag(BagOfAll(balOf, SetToBag(topBlocks))) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

(***************************************************************************)
(* Creates the genesis block.                                              *)
(***************************************************************************)

CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey]
        genesisBlock ==
            [type |-> "genesis", account |-> publicKey, balance |-> GenesisBalance]
    IN /\ ~GenesisBlockExists
       /\ CalculateHash(genesisBlock, lastHash, lastHash')
       /\ distributedLedger' =
            [n \in Node |->
                [distributedLedger[n] EXCEPT
                     ![lastHash'] =
                        [block |-> genesisBlock,
                         signature |-> SignHash(lastHash', privateKey)]]]
       /\ UNCHANGED received

(***************************************************************************)
(* Creation, validation, and confirmation of open blocks. Checks include:  *)
(*  - The block is signed by the private key of the account being opened   *)
(*  - The node's ledger contains the referenced source block               *)
(*  - The source block is a send block to the account being opened         *)
(***************************************************************************)

ValidateOpenBlock(ledger, block) ==
    /\ block.type = "open"
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = block.account

CreateOpenBlock(node) ==
    LET privateKey == Ownership[node]
        publicKey == KeyPair[privateKey]
        ledger == distributedLedger[node]
    IN \E rep \in PublicKey : \E src \in Hash :
           LET newOpenBlock ==
                 [account |-> publicKey, source |-> src,
                  rep |-> rep, type |-> "open"]
           IN /\ ValidateOpenBlock(ledger, newOpenBlock)
              /\ CalculateHash(newOpenBlock, lastHash, lastHash')
              /\ received' =
                   [n \in Node |->
                        IF n = node
                        THEN received[n] \cup {[block |-> newOpenBlock,
                                                signature |-> SignHash(lastHash', privateKey)}]
                        ELSE received[n]]
              /\ UNCHANGED distributedLedger

ProcessOpenBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node]
        block == signedBlock.block
    IN /\ ValidateOpenBlock(ledger, block)
       /\ ~IsAccountOpen(ledger, block.account)
       /\ CalculateHash(block, lastHash, lastHash')
       /\ ValidateSignature(signedBlock.signature, block.account, lastHash')
       /\ distributedLedger' =
            [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
       /\ received' = [received EXCEPT ![node] = received[node] \ {signedBlock}]

(***************************************************************************)
(* Creation, validation, and confirmation of send blocks. Checks include:  *)
(*  - The node's ledger contains the referenced previous block             *)
(*  - The block is signed by the account sourcing the funds                *)
(*  - The value sent is non-negative                                       *)
(***************************************************************************)

ValidateSendBlock(ledger, block) ==
    /\ block.type = "send"
    /\ ledger[block.previous] /= NoBlock
    /\ block.balance <= BalanceAt(ledger, block.previous)

CreateSendBlock(node) ==
    LET privateKey == Ownership[node]
        publicKey == KeyPair[privateKey]
        ledger == distributedLedger[node]
    IN \E prev \in Hash : \E recipient \in PublicKey : \E bal \in AccountBalance :
           LET newSendBlock ==
                 [previous |-> prev, balance |-> bal,
                  destination |-> recipient, type |-> "send"]
           IN /\ ledger[prev] /= NoBlock
              /\ PublicKeyOf(ledger, prev) = publicKey
              /\ ValidateSendBlock(ledger, newSendBlock)
              /\ CalculateHash(newSendBlock, lastHash, lastHash')
              /\ received' =
                   [n \in Node |->
                        IF n = node
                        THEN received[n] \cup {[block |-> newSendBlock,
                                                signature |-> SignHash(lastHash', privateKey)}]
                        ELSE received[n]]
              /\ UNCHANGED distributedLedger

ProcessSendBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node]
        block == signedBlock.block
    IN /\ ValidateSendBlock(ledger, block)
       /\ CalculateHash(block, lastHash, lastHash')
       /\ ValidateSignature(signedBlock.signature,
                            PublicKeyOf(ledger, block.previous), lastHash')
       /\ distributedLedger' =
            [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
       /\ received' = [received EXCEPT ![node] = received[node] \ {signedBlock}]

(***************************************************************************)
(* Creation, validation, & confirmation of receive blocks. Checks include: *)
(*  - The node's ledger contains the referenced previous & source blocks   *)
(*  - The block is signed by the account sourcing the funds                *)
(*  - The source block is a send block to the receive block's account      *)
(*  - The source block does not already have a corresponding receive/open  *)
(***************************************************************************)

ValidateReceiveBlock(ledger, block) ==
    /\ block.type = "receive"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = PublicKeyOf(ledger, block.previous)
    /\ ~IsSendReceived(ledger, block.source)

CreateReceiveBlock(node) ==
    LET privateKey == Ownership[node]
        publicKey == KeyPair[privateKey]
        ledger == distributedLedger[node]
    IN \E prev \in Hash : \E src \in Hash :
           LET newRcvBlock ==
                 [previous |-> prev, source |-> src, type |-> "receive"]
           IN /\ ValidateReceiveBlock(ledger, newRcvBlock)
              /\ PublicKeyOf(ledger, prev) = publicKey
              /\ CalculateHash(newRcvBlock, lastHash, lastHash')
              /\ received' =
                   [n \in Node |->
                        IF n = node
                        THEN received[n] \cup {[block |-> newRcvBlock,
                                                signature |-> SignHash(lastHash', privateKey)}]
                        ELSE received[n]]
              /\ UNCHANGED distributedLedger

ProcessReceiveBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node]
        block == signedBlock.block
    IN /\ ValidateReceiveBlock(ledger, block)
       /\ ~IsSendReceived(ledger, block.source)
       /\ CalculateHash(block, lastHash, lastHash')
       /\ ValidateSignature(signedBlock.signature,
                            PublicKeyOf(ledger, block.previous), lastHash')
       /\ distributedLedger' =
            [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
       /\ received' = [received EXCEPT ![node] = received[node] \ {signedBlock}]

(***************************************************************************)
(* Creation, validation, & confirmation of change blocks. Checks include:  *)
(*  - The node's ledger contains the referenced previous block             *)
(*  - The block is signed by the correct account                           *)
(***************************************************************************)

ValidateChangeBlock(ledger, block) ==
    /\ block.type = "change"
    /\ ledger[block.previous] /= NoBlock

CreateChangeRepBlock(node) ==
    LET privateKey == Ownership[node]
        publicKey == KeyPair[privateKey]
        ledger == distributedLedger[node]
    IN \E prev \in Hash : \E newRep \in PublicKey :
           LET newChangeBlock ==
                 [previous |-> prev, rep |-> newRep, type |-> "change"]
           IN /\ ValidateChangeBlock(ledger, newChangeBlock)
              /\ PublicKeyOf(ledger, prev) = publicKey
              /\ CalculateHash(newChangeBlock, lastHash, lastHash')
              /\ received' =
                   [n \in Node |->
                        IF n = node
                        THEN received[n] \cup {[block |-> newChangeBlock,
                                                signature |-> SignHash(lastHash', privateKey)}]
                        ELSE received[n]]
              /\ UNCHANGED distributedLedger

ProcessChangeRepBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node]
        block == signedBlock.block
    IN /\ ValidateChangeBlock(ledger, block)
       /\ CalculateHash(block, lastHash, lastHash')
       /\ ValidateSignature(signedBlock.signature,
                            PublicKeyOf(ledger, block.previous), lastHash')
       /\ distributedLedger' =
            [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
       /\ received' = [received EXCEPT ![node] = received[node] \ {signedBlock}]

(***************************************************************************)
(* Top-level actions.                                                      *)
(***************************************************************************)

CreateBlock(node) ==
    \/ CreateOpenBlock(node) \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node) \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E block \in received[node] :
         ProcessOpenBlock(node, block) \/ ProcessSendBlock(node, block)
         \/ ProcessReceiveBlock(node, block) \/ ProcessChangeRepBlock(node, block)
       /\ received' = [received EXCEPT ![node] = received[node] \ {block}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E k \in PrivateKey : CreateGenesisBlock(k)
    \/ \E n \in Node : CreateBlock(n) \/ ProcessBlock(n)

Spec == /\ Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

====