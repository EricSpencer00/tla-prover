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

ValidateSignature(sig, expectedPublicKey, expectedHash) ==
    LET pub == KeyPair[sig.signedWith] IN
    /\ pub = expectedPublicKey
    /\ sig.data = expectedHash

(***************************************************************************)
(* Block definitions                                                       *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type    |-> "genesis",
     account |-> PublicKey,   \* placeholder; actual value set in CreateGenesisBlock
     balance |-> GenesisBalance]

SendBlock ==
    [previous    |-> Hash,
     balance     |-> AccountBalance,
     destination |-> PublicKey,
     type        |-> "send"]

OpenBlock ==
    [account   |-> PublicKey,
     source    |-> Hash,
     rep       |-> PublicKey,
     type      |-> "open"]

ReceiveBlock ==
    [previous |-> Hash,
     source   |-> Hash,
     type     |-> "receive"]

ChangeRepBlock ==
    [previous |-> Hash,
     rep      |-> PublicKey,
     type     |-> "change"]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b \in [type : {"none"}] : TRUE   \* dummy record
NoHash  == CHOOSE h \in Hash : TRUE                \* dummy hash

Ledger == [Hash -> (SignedBlock \cup {NoBlock})]

(***************************************************************************)
(* Utility functions                                                       *)
(***************************************************************************)

GenesisBlockExists == lastHash # NoHash

IsAccountOpen(ledger, pk) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
        sb # NoBlock /\ sb.block.type \in {"genesis", "open"} /\ sb.block.account = pk

IsSendReceived(ledger, src) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
        sb # NoBlock /\ sb.block.type \in {"open", "receive"} /\ sb.block.source = src

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, h) ==
    LET sb == ledger[h] IN
    LET b  == sb.block IN
    IF b.type \in {"genesis", "open"}
       THEN b.account
       ELSE PublicKeyOf(ledger, b.previous)

TopBlock(ledger, pk) ==
    CHOOSE h \in Hash :
        LET sb == ledger[h] IN
        sb # NoBlock /\
        PublicKeyOf(ledger, h) = pk /\
        ~\E h2 \in Hash :
            LET sb2 == ledger[h2] IN
            sb2 # NoBlock /\ sb2.block.type \in {"send", "receive", "change"} /\ sb2.block.previous = h

RECURSIVE BalanceAt(_, _)
RECURSIVE ValueOfSendBlock(_, _)

BalanceAt(ledger, h) ==
    LET sb == ledger[h] IN
    LET b  == sb.block IN
    CASE b.type = "open"   -> ValueOfSendBlock(ledger, b.source)
    []   b.type = "send"   -> b.balance
    []   b.type = "receive" ->
          BalanceAt(ledger, b.previous) + ValueOfSendBlock(ledger, b.source)
    []   b.type = "change" -> BalanceAt(ledger, b.previous)
    []   b.type = "genesis" -> b.balance

ValueOfSendBlock(ledger, h) ==
    LET sb == ledger[h] IN
    LET b  == sb.block IN
    BalanceAt(ledger, b.previous) - b.balance

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE LET e == CHOOSE x \in S : TRUE IN e + SumBag(B \ {e})

(***************************************************************************)
(* Invariants                                                               *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A n \in Node :
          LET ledger == distributedLedger[n] IN
          \A h \in Hash :
            LET sb == ledger[h] IN
            sb # NoBlock =>
                LET pk == PublicKeyOf(ledger, h) IN
                ValidateSignature(sb.signature, pk, h)

BalanceInvariant ==
    /\ \A n \in Node :
          LET ledger == distributedLedger[n] IN
          LET openAccs == {pk \in PublicKey : IsAccountOpen(ledger, pk)} IN
          LET topBlks  == {TopBlock(ledger, pk) : pk \in openAccs} IN
          LET acctBals == {BalanceAt(ledger, h) : h \in topBlks} IN
          SumBag(acctBals) <= GenesisBalance

SafetyInvariant == CryptographicInvariant

(***************************************************************************)
(* Genesis block creation                                                   *)
(***************************************************************************)

CreateGenesisBlock(priv) ==
    LET pub == KeyPair[priv] IN
    LET genBlock == [type |-> "genesis",
                     account |-> pub,
                     balance |-> GenesisBalance] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(genBlock, lastHash, newHash)
    /\ distributedLedger' =
        [n \in Node |-> [h \in Hash |-> NoBlock]]
        [n \in Node |-> [h \in Hash |-> IF h = newHash THEN
                         [block |-> genBlock,
                          signature |-> SignHash(newHash, priv)]
                         ELSE NoBlock]]
    /\ lastHash' = newHash
    /\ UNCHANGED received

(***************************************************************************)
(* Block creation helpers                                                   *)
(***************************************************************************)

ValidateOpenBlock(ledger, blk) ==
    /\ blk.type = "open"
    /\ ledger[blk.source] # NoBlock
    /\ ledger[blk.source].block.type = "send"
    /\ ledger[blk.source].block.destination = blk.account

CreateOpenBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    /\ \E src \in Hash :
        /\ ledger[src] # NoBlock
        /\ ledger[src].block.type = "send"
        /\ ledger[src].block.destination = pub
        /\ \E rep \in PublicKey :
            LET blk == [type |-> "open",
                        account |-> pub,
                        source |-> src,
                        rep |-> rep] IN
            /\ ValidateOpenBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, newHash)
            /\ received' =
                [n \in Node |-> IF n = node
                              THEN received[n] \cup
                                   {[block |-> blk,
                                     signature |-> SignHash(newHash, priv)]}
                              ELSE received[n]]
            /\ UNCHANGED <<lastHash, distributedLedger>>

ProcessOpenBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk == sb.block IN
    /\ ValidateOpenBlock(ledger, blk)
    /\ ~IsAccountOpen(ledger, blk.account)
    /\ CalculateHash(blk, lastHash, newHash)
    /\ ValidateSignature(sb.signature, blk.account, newHash)
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][newHash] = sb]
    /\ lastHash' = newHash
    /\ UNCHANGED received

ValidateSendBlock(ledger, blk) ==
    /\ blk.type = "send"
    /\ ledger[blk.previous] # NoBlock
    /\ blk.balance <= BalanceAt(ledger, blk.previous)

CreateSendBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prev \in Hash :
        /\ ledger[prev] # NoBlock
        /\ PublicKeyOf(ledger, prev) = pub
        /\ \E rec \in PublicKey :
            /\ \E bal \in AccountBalance :
                LET blk == [type |-> "send",
                            previous |-> prev,
                            balance |-> bal,
                            destination |-> rec] IN
                /\ ValidateSendBlock(ledger, blk)
                /\ CalculateHash(blk, lastHash, newHash)
                /\ received' =
                    [n \in Node |-> IF n = node
                                  THEN received[n] \cup
                                       {[block |-> blk,
                                         signature |-> SignHash(newHash, priv)]}
                                  ELSE received[n]]
                /\ UNCHANGED <<lastHash, distributedLedger>>

ProcessSendBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk == sb.block IN
    /\ ValidateSendBlock(ledger, blk)
    /\ CalculateHash(blk, lastHash, newHash)
    /\ ValidateSignature(sb.signature,
                         PublicKeyOf(ledger, blk.previous),
                         newHash)
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][newHash] = sb]
    /\ lastHash' = newHash
    /\ UNCHANGED received

ValidateReceiveBlock(ledger, blk) ==
    /\ blk.type = "receive"
    /\ ledger[blk.previous] # NoBlock
    /\ ledger[blk.source]   # NoBlock
    /\ ledger[blk.source].block.type = "send"
    /\ ledger[blk.source].block.destination =
       PublicKeyOf(ledger, blk.previous)

CreateReceiveBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prev \in Hash :
        /\ ledger[prev] # NoBlock
        /\ PublicKeyOf(ledger, prev) = pub
        /\ \E src \in Hash :
            LET blk == [type |-> "receive",
                        previous |-> prev,
                        source |-> src] IN
            /\ ValidateReceiveBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, newHash)
            /\ received' =
                [n \in Node |-> IF n = node
                              THEN received[n] \cup
                                   {[block |-> blk,
                                     signature |-> SignHash(newHash, priv)]}
                              ELSE received[n]]
            /\ UNCHANGED <<lastHash, distributedLedger>>

ProcessReceiveBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk == sb.block IN
    /\ ValidateReceiveBlock(ledger, blk)
    /\ ~IsSendReceived(ledger, blk.source)
    /\ CalculateHash(blk, lastHash, newHash)
    /\ ValidateSignature(sb.signature,
                         PublicKeyOf(ledger, blk.previous),
                         newHash)
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][newHash] = sb]
    /\ lastHash' = newHash
    /\ UNCHANGED received

ValidateChangeBlock(ledger, blk) ==
    /\ blk.type = "change"
    /\ ledger[blk.previous] # NoBlock

CreateChangeRepBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prev \in Hash :
        /\ ledger[prev] # NoBlock
        /\ PublicKeyOf(ledger, prev) = pub
        /\ \E newRep \in PublicKey :
            LET blk == [type |-> "change",
                        previous |-> prev,
                        rep |-> newRep] IN
            /\ ValidateChangeBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, newHash)
            /\ received' =
                [n \in Node |-> IF n = node
                              THEN received[n] \cup
                                   {[block |-> blk,
                                     signature |-> SignHash(newHash, priv)]}
                              ELSE received[n]]
            /\ UNCHANGED <<lastHash, distributedLedger>>

ProcessChangeRepBlock(node, sb) ==
    LET ledger == distributedLedger[node] IN
    LET blk == sb.block IN
    /\ ValidateChangeBlock(ledger, blk)
    /\ CalculateHash(blk, lastHash, newHash)
    /\ ValidateSignature(sb.signature,
                         PublicKeyOf(ledger, blk.previous),
                         newHash)
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node][newHash] = sb]
    /\ lastHash' = newHash
    /\ UNCHANGED received

(***************************************************************************)
(* Top‑level actions                                                       *)
(***************************************************************************)

CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E sb \in received[node] :
          ( \/ ProcessOpenBlock(node, sb)
            \/ ProcessSendBlock(node, sb)
            \/ ProcessReceiveBlock(node, sb)
            \/ ProcessChangeRepBlock(node, sb) )
    /\ received' = [received EXCEPT ![node] = @ \ {sb}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E priv \in PrivateKey : CreateGenesisBlock(priv)
    \/ \E n \in Node : CreateBlock(n)
    \/ \E n \in Node : ProcessBlock(n)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

====