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
    /\ \A data, oldHash, newHash :
        /\ CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

(***************************************************************************)
(* Functions to sign hashes with private key and validate signatures       *)
(* against public key.                                                     *)
(***************************************************************************)

Signature == [data : Hash, signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data |-> hash,
     signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

(***************************************************************************)
(* Block definitions                                                       *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type |-> "genesis",
     account |-> PUBLICKEY_PLACEHOLDER,
     balance |-> GenesisBalance]

SendBlock ==
    [previous |-> NOHASH_PLACEHOLDER,
     balance |-> 0,
     destination |-> PUBLICKEY_PLACEHOLDER,
     type |-> "send"]

OpenBlock ==
    [account |-> PUBLICKEY_PLACEHOLDER,
     source |-> NOHASH_PLACEHOLDER,
     rep |-> PUBLICKEY_PLACEHOLDER,
     type |-> "open"]

ReceiveBlock ==
    [previous |-> NOHASH_PLACEHOLDER,
     source |-> NOHASH_PLACEHOLDER,
     type |-> "receive"]

ChangeRepBlock ==
    [previous |-> NOHASH_PLACEHOLDER,
     rep |-> PUBLICKEY_PLACEHOLDER,
     type |-> "change"]

Block == 
    {GenesisBlock} \cup
    {SendBlock} \cup
    {OpenBlock} \cup
    {ReceiveBlock} \cup
    {ChangeRepBlock}

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock

NoHash == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(***************************************************************************)
(* Utility functions                                                       *)
(***************************************************************************)

GenesisBlockExists == lastHash /= NoHash

IsAccountOpen(ledger, publicKey) ==
    \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ signedBlock.block.type \in {"genesis", "open"}
        /\ signedBlock.block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ signedBlock.block.type \in {"open", "receive"}
        /\ signedBlock.block.source = sourceHash

RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, blockHash) ==
    LET signedBlock == ledger[blockHash]
        block == signedBlock.block
    IN IF block.type \in {"genesis", "open"}
       THEN block.account
       ELSE PublicKeyOf(ledger, block.previous)

TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ ~\E otherHash \in Hash :
            LET otherSignedBlock == ledger[otherHash] IN
            /\ otherSignedBlock /= NoBlock
            /\ otherSignedBlock.block.type \in {"send", "receive", "change"}
            /\ otherSignedBlock.block.previous = hash

RECURSIVE BalanceAt(_,_)
RECURSIVE ValueOfSendBlock(_,_)

BalanceAt(ledger, hash) ==
    LET signedBlock == ledger[hash]
        block == signedBlock.block
    IN
    CASE block.type = "open" -> ValueOfSendBlock(ledger, block.source)
    [] block.type = "send" -> block.balance
    [] block.type = "receive" ->
        BalanceAt(ledger, block.previous) + ValueOfSendBlock(ledger, block.source)
    [] block.type = "change" -> BalanceAt(ledger, block.previous)
    [] block.type = "genesis" -> block.balance

ValueOfSendBlock(ledger, hash) ==
    LET signedBlock == ledger[hash]
        block == signedBlock.block
    IN BalanceAt(ledger, block.previous) - block.balance

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        /\ \A hash \in Hash :
            LET signedBlock == ledger[hash] IN
            signedBlock /= NoBlock =>
                LET publicKey == PublicKeyOf(ledger, hash) IN
                ValidateSignature(signedBlock.signature, publicKey, hash)

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE
        LET e == CHOOSE x \in S : TRUE IN
        e + SumBag(B \ {e})

BalanceInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        LET openAccounts == {a \in PublicKey : IsAccountOpen(ledger, a)} IN
        LET topBlocks == {TopBlock(ledger, a) : a \in openAccounts} IN
        LET accountBalances ==
            LET ledgerBalanceAt(hash) == BalanceAt(ledger, hash) IN
            BagOfAll(ledgerBalanceAt, SetToBag(topBlocks))
        IN
        IF GenesisBlockExists
        THEN SumBag(accountBalances) <= GenesisBalance
        ELSE TRUE

SafetyInvariant == CryptographicInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey] IN
    LET genesisBlock ==
        [type |-> "genesis",
         account |-> publicKey,
         balance |-> GenesisBalance] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(genesisBlock, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |-> 
            [h \in Hash |-> 
                IF h = lastHash' THEN
                    [block |-> genesisBlock,
                     signature |-> SignHash(lastHash', privateKey)]
                ELSE NoBlock]]
    /\ UNCHANGED received

ValidateOpenBlock(ledger, block) ==
    /\ block.type = "open"
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = block.account

CreateOpenBlock(node) ==
    LET privateKey == Ownership[node] IN
    LET publicKey == KeyPair[privateKey] IN
    LET ledger == distributedLedger[node] IN
    /\ \E repPublicKey \in PublicKey :
        \E srcHash \in Hash :
            LET newOpenBlock ==
                [account |-> publicKey,
                 source |-> srcHash,
                 rep |-> repPublicKey,
                 type |-> "open"] IN
            /\ ValidateOpenBlock(ledger, newOpenBlock)
            /\ CalculateHash(newOpenBlock, lastHash, lastHash')
            /\ received' =
                [n \in Node |-> 
                    IF n = node
                    THEN received[n] \cup {
                        [block |-> newOpenBlock,
                         signature |-> SignHash(lastHash', privateKey)}]
                    ELSE received[n]]
            /\ UNCHANGED distributedLedger

ProcessOpenBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node]
        block == signedBlock.block
    IN
    /\ ValidateOpenBlock(ledger, block)
    /\ ~IsAccountOpen(ledger, block.account)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(signedBlock.signature, block.account, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
    /\ UNCHANGED received

ValidateSendBlock(ledger, block) ==
    /\ block.type = "send"
    /\ ledger[block.previous] /= NoBlock
    /\ block.balance <= BalanceAt(ledger, block.previous)

CreateSendBlock(node) ==
    LET privateKey == Ownership[node] IN
    LET publicKey == KeyPair[privateKey] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prevHash \in Hash :
        ledger[prevHash] /= NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E recipient \in PublicKey :
            \E newBalance \in AccountBalance :
                LET newSendBlock ==
                    [previous |-> prevHash,
                     balance |-> newBalance,
                     destination |-> recipient,
                     type |-> "send"] IN
                /\ ValidateSendBlock(ledger, newSendBlock)
                /\ CalculateHash(newSendBlock, lastHash, lastHash')
                /\ received' =
                    [n \in Node |-> 
                        IF n = node
                        THEN received[n] \cup {
                            [block |-> newSendBlock,
                             signature |-> SignHash(lastHash', privateKey)}]
                        ELSE received[n]]
                /\ UNCHANGED distributedLedger

ProcessSendBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node]
        block == signedBlock.block
    IN
    /\ ValidateSendBlock(ledger, block)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(
          signedBlock.signature,
          PublicKeyOf(ledger, block.previous),
          lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
    /\ UNCHANGED received

ValidateReceiveBlock(ledger, block) ==
    /\ block.type = "receive"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination =
       PublicKeyOf(ledger, block.previous)

CreateReceiveBlock(node) ==
    LET privateKey == Ownership[node] IN
    LET publicKey == KeyPair[privateKey] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prevHash \in Hash :
        ledger[prevHash] /= NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E srcHash \in Hash :
            LET newRcvBlock ==
                [previous |-> prevHash,
                 source |-> srcHash,
                 type |-> "receive"] IN
            /\ ValidateReceiveBlock(ledger, newRcvBlock)
            /\ CalculateHash(newRcvBlock, lastHash, lastHash')
            /\ received' =
                [n \in Node |-> 
                    IF n = node
                    THEN received[n] \cup {
                        [block |-> newRcvBlock,
                         signature |-> SignHash(lastHash', privateKey)}]
                    ELSE received[n]]
            /\ UNCHANGED distributedLedger

ProcessReceiveBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node]
        block == signedBlock.block
    IN
    /\ ValidateReceiveBlock(ledger, block)
    /\ ~IsSendReceived(ledger, block.source)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(
          signedBlock.signature,
          PublicKeyOf(ledger, block.previous),
          lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
    /\ UNCHANGED received

ValidateChangeBlock(ledger, block) ==
    /\ block.type = "change"
    /\ ledger[block.previous] /= NoBlock

CreateChangeRepBlock(node) ==
    LET privateKey == Ownership[node] IN
    LET publicKey == KeyPair[privateKey] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prevHash \in Hash :
        ledger[prevHash] /= NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E newRep \in PublicKey :
            LET newChangeRepBlock ==
                [previous |-> prevHash,
                 rep |-> newRep,
                 type |-> "change"] IN
            /\ ValidateChangeBlock(ledger, newChangeRepBlock)
            /\ CalculateHash(newChangeRepBlock, lastHash, lastHash')
            /\ received' =
                [n \in Node |-> 
                    IF n = node
                    THEN received[n] \cup {
                        [block |-> newChangeRepBlock,
                         signature |-> SignHash(lastHash', privateKey)}]
                    ELSE received[n]]
            /\ UNCHANGED distributedLedger

ProcessChangeRepBlock(node, signedBlock) ==
    LET ledger == distributedLedger[node]
        block == signedBlock.block
    IN
    /\ ValidateChangeBlock(ledger, block)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(
          signedBlock.signature,
          PublicKeyOf(ledger, block.previous),
          lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][lastHash'] = signedBlock]
    /\ UNCHANGED received

CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E block \in received[node] :
        /\ (  ProcessOpenBlock(node, block)
            \/ ProcessSendBlock(node, block)
            \/ ProcessReceiveBlock(node, block)
            \/ ProcessChangeRepBlock(node, block))
        /\ received' = [received EXCEPT ![node] = @ \ {block}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E account \in PrivateKey : CreateGenesisBlock(account)
    \/ \E node \in Node : CreateBlock(node)
    \/ \E node \in Node : ProcessBlock(node)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

====