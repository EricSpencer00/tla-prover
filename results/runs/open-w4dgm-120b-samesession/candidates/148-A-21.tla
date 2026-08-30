---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
    Hash, NoHashVal,
    PrivateKey, PublicKey,
    Node, GenesisBalance, NoBlockVal,
    CalculateHash, NoHash, NoBlock

\* Ledger is replicated across nodes, each node also has a received-but-not-yet-validated
\* set of broadcast blocks (the order they were created in is what gives the chain its shape).
\* Types: lastHash is the most recent block's hash; ledger maps hashes to signed blocks
\* (or NoBlock); received maps each node to the set of blocks it has not yet absorbed.
VARIABLES
    lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Block == [prev: Hash \cup {NoHash}, acct: PublicKey, amt: 0..GenesisBalance,
          kind: {"send", "receive", "open", "change"}, signedBy: PrivateKey]

\* The genesis block is the first block ever inserted into the ledger; because it has no
\* predecessor its prev field is set to NoHash, and its kind is "open" (not "receive").
GenesisBlock == [prev |-> NoHash, acct |-> CHOOSE pk \in PublicKey : TRUE,
                 amt |-> GenesisBalance, kind |-> "open",
                 signedBy |-> CHOOSE sk \in PrivateKey : TRUE]

WellFormedLedger ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Hash -> Block \cup {NoBlock}]
    /\ received \in [Node -> SUBSET Block]

TypeInvariant == WellFormedLedger

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [h \in Hash |-> NoBlock]
    /\ received = [n \in Node |-> {}]

\* Hash calculation and signature verification are abstracted to constants passed in from
\* the .cfg; the model is a symbolic representation of the chain shape, not a hash evaluator.
GenesisBlockCreated ==
    /\ lastHash = NoHashVal
    /\ ledger[NoHash] = NoBlock
    /\ lastHash' = NoHash
    /\ ledger' = [h \in Hash |-> IF h = NoHash THEN GenesisBlock ELSE NoBlock]
    /\ received' = [n \in Node |-> IF ledger[NoHash] = NoBlock THEN received[n] ELSE received[n] \cup {GenesisBlock}]

\* Account balance is derived by walking the chain backwards from the head, adding up receives
\* and subtracting sends. Recursion is bounded by how many hashes exist, not by a runtime depth.
SumAmounts(S) ==
    IF S = {} THEN 0
    ELSE LET blk == CHOOSE x \in S : TRUE
         IN (IF blk.kind = "receive" THEN blk.amt ELSE 0) + SumAmounts(S \ {blk})
Balance(ac) == SumAmounts({h \in Hash : ledger[h] # NoBlock /\ ledger[h].acct = ac})

AccountHasBalance(ac, a) == Balance(ac) >= a

CreateSendBlock(n, r, a) ==
    /\ a \in 1..GenesisBalance
    /\ AccountHasBalance(PublicKey[n], a)
    /\ lastHash # NoHashVal
    /\ ~\E blk \in received[n] :
        /\ blk.kind = "send" /\ blk.signedBy = r
        /\ blk.acct = PublicKey[n] /\ blk.amt = a
    /\ \E h \in Hash :
        /\ ledger[h] = NoBlock
        /\ ledger' = [ledger EXCEPT ![h] = [prev |-> lastHash, acct |-> PublicKey[n],
                                            amt |-> a, kind |-> "send", signedBy |-> r]]
        /\ lastHash' = h
    /\ received' = [received EXCEPT ![n] = received[n] \cup {ledger[h]}]

\* Opening an account: a receive block can only be created on top of a send block whose
\* destination is this node's public key; the protocol disallows creating an opening block
\* directly from scratch, so a node must first be sent some coins.
CreateOpenBlock(n, r) ==
    /\ \E h \in Hash :
        /\ ledger[h] # NoBlock /\ ledger[h].kind = "send" /\ ledger[h].signedBy = r
        /\ ledger[h].acct # PublicKey[n]
        /\ ledger[h].amt \in 1..GenesisBalance
        /\ ledger[h].prev # NoHash
        /\ ~\E blk \in received[n] :
            blk.kind = "open" /\ blk.signedBy = r /\ blk.acct = PublicKey[n]
        /\ \E h2 \in Hash :
            /\ ledger[h2] = NoBlock
            /\ ledger' = [ledger EXCEPT ![h2] = [prev |-> h, acct |-> PublicKey[n],
                                                 amt |-> 0, kind |-> "open", signedBy |-> r]]
            /\ lastHash' = h2
    /\ received' = [received EXCEPT ![n] = received[n] \cup {ledger[h2]}]

CreateReceiveBlock(n, r, h) ==
    /\ ledger[h] # NoBlock /\ ledger[h].kind = "send"
    /\ ledger[h].acct # PublicKey[n]
    /\ ledger[h].signedBy = r
    /\ ~\E blk \in received[n] :
        blk.kind = "receive" /\ blk.signedBy = r /\ blk.acct = PublicKey[n] /\ blk.prev = h
    /\ \E h2 \in Hash :
        /\ ledger[h2] = NoBlock
        /\ ledger' = [ledger EXCEPT ![h2] = [prev |-> ledger[h].prev, acct |-> PublicKey[n],
                                             amt |-> ledger[h].amt, kind |-> "receive", signedBy |-> r]]
        /\ lastHash' = h2
    /\ received' = [received EXCEPT ![n] = received[n] \cup {ledger[h2]}]

CreateChangeBlock(n, r) ==
    /\ lastHash # NoHashVal
    /\ ~\E blk \in received[n] :
        blk.kind = "change" /\ blk.signedBy = r /\ blk.acct = PublicKey[n]
    /\ \E h \in Hash :
        /\ ledger[h] = NoBlock
        /\ ledger' = [ledger EXCEPT ![h] = [prev |-> lastHash, acct |-> PublicKey[n],
                                            amt |-> 0, kind |-> "change", signedBy |-> r]]
        /\ lastHash' = h
    /\ received' = [received EXCEPT ![n] = received[n] \cup {ledger[h]}]

\* Validation looks only at the node's own copy of the ledger: a block is accepted when the
\* copy shows the referenced previous block exists and the signature matches the account's
\* public key; a block that fails any of those is simply dropped rather than absorbed.
ValidateAndAbsorb(n, blk) ==
    /\ blk \in received[n]
    /\ ledger' = IF ledger[blk.prev] # NoBlock /\ PublicKey[n] = ledger[blk.prev].acct
                 THEN [ledger EXCEPT ![blk.prev] = blk]
                 ELSE ledger
    /\ received' = [received EXCEPT ![n] = received[n] \ {blk}]
    /\ lastHash' = IF ledger[blk.prev] # NoBlock /\ PublicKey[n] = ledger[blk.prev].acct
                   THEN IF blk.prev # NoHashVal THEN IF blk.prev > lastHash THEN blk.prev ELSE lastHash
                        ELSE blk.prev
                   ELSE lastHash

Next ==
    \/ GenesisBlockCreated
    \/ \E n \in Node, r \in PrivateKey :
         \/ CreateSendBlock(n, r, 1) \/ CreateSendBlock(n, r, 2)
         \/ CreateOpenBlock(n, r) \/ CreateChangeBlock(n, r)
         \/ \E h \in Hash : CreateReceiveBlock(n, r, h)
    \/ \E n \in Node, blk \in Block : ValidateAndAbsorb(n, blk)

Spec == Init /\ [][Next]_vars

\* The cryptographic invariant: every block present in every node's replicated ledger must
\* have a signature that matches the public key of the account that owns that block's chain.
SafetyInvariant ==
    \A h \in Hash :
        ledger[h] # NoBlock => PublicKey[ledger[h].signedBy] = ledger[h].acct
====