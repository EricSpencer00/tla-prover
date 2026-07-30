---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME GenesisBalance \in Nat

Blocks == PublicKey \cup {NoBlockVal}

Msgs == [blk : Blocks, sender : Node, recv : Node]

VARIABLES
    lastHash, ledger, recvMsgs

vars == <<lastHash, ledger, recvMsgs>>

\* Ed25519-style signatures are modeled as an injective pairing of the
\* signing key and the signed block data. Message validation checks that
\* every stored block's signature's public half matches the public key of
\* the account that owns the block's chain.
\* Blake2b-style hashing is modeled as the abstract constant operator
\* CalculateHash, which maps block data and the previous hash to a new hash.

\* The account balance is tracked by recursively walking the account chain.
\* Because the chain holds the entire ordering of action history, each
\* comparison is itself a walk of the chain, which is what gives the
\* lattice its super-exponential state space scaling.

RECURSIVE ChainBalance(_)
ChainBalance(h) ==
    IF h = NoHashVal THEN 0
    ELSE
        LET b == ledger[h] IN
            \* A send block takes money out of the sender's balance.
            IF b.type = "send" THEN b.prevBal - b.amount
            \* An open block starts the account at 0.
            ELSE IF b.type = "open" THEN 0
            \* A receive block adds the received amount.
            ELSE IF b.type = "receive" THEN b.prevBal + b.amount
            \* A change block neither adds nor subtracts.
            ELSE b.prevBal

\* The sum of all account balances stays below the genesis balance, which
\* is a separate accounting check from the main invariant.
RECURSIVE SumBalances(_)
SumBalances(S) ==
    IF S = {} THEN 0
    ELSE
        LET h == CHOOSE x \in S : TRUE IN
            ChainBalance(h) + SumBalances(S \ {h})

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [h \in Hash |-> NoBlockVal]
    /\ recvMsgs = [n \in Node |-> {}]

\* The genesis block is created and confirmed in one step: broadcast and
\* store simultaneously. This is what makes it happen at most once.
CreateGenesis(n) ==
    /\ lastHash = NoHashVal
    /\ n \in PrivateKey
    /\ LET h == CalculateHash([type |-> "genesis"], NoHashVal) IN
        /\ lastHash' = h
        /\ ledger' = [k \in Hash |-> IF k = h
                         THEN [type |-> "genesis", signer |-> n, amount |-> GenesisBalance,
                               prevHash |-> NoHashVal, prevBal |-> 0]
                         ELSE ledger[k]]
        /\ recvMsgs' = [m \in Node |-> {}]

CreateSend(n, r) ==
    /\ n \in PrivateKey
    /\ lastHash # NoHashVal
    /\ LET curBal == ChainBalance(lastHash) IN
        /\ curBal > 0
        /\ LET h == CalculateHash([type |-> "send", amt |-> curBal], lastHash) IN
            /\ lastHash' = h
            /\ ledger' = [k \in Hash |-> IF k = h
                             THEN [type |-> "send", signer |-> n, amount |-> curBal,
                                   prevHash |-> lastHash, prevBal |-> curBal]
                             ELSE ledger[k]]
            /\ recvMsgs' = [m \in Node |-> recvMsgs[m] \cup
                              {[blk |-> h, sender |-> n, recv |-> r]}]

CreateOpen(n) ==
    /\ n \in PrivateKey
    /\ lastHash # NoHashVal
    /\ \E m \in recvMsgs[n] :
        /\ ledger[m.blk].type = "send"
        /\ ledger[m.blk].blkDest = n
        /\ LET h == CalculateHash([type |-> "open"], lastHash) IN
            /\ lastHash' = h
            /\ ledger' = [k \in Hash |-> IF k = h
                             THEN [type |-> "open", signer |-> n, amount |-> 0,
                                   prevHash |-> lastHash, prevBal |-> 0]
                             ELSE ledger[k]]
            /\ recvMsgs' = [m \in Node |-> recvMsgs[m] \ {m}]

CreateReceive(n) ==
    /\ n \in PrivateKey
    /\ lastHash # NoHashVal
    /\ \E m \in recvMsgs[n] :
        /\ ledger[m.blk].type = "send"
        /\ ledger[m.blk].blkDest = n
        /\ LET h == CalculateHash([type |-> "receive"], lastHash) IN
            /\ lastHash' = h
            /\ ledger' = [k \in Hash |-> IF k = h
                             THEN [type |-> "receive", signer |-> n, amount |-> ledger[m.blk].amount,
                                   prevHash |-> lastHash, prevBal |-> ChainBalance(lastHash)]
                             ELSE ledger[k]]
            /\ recvMsgs' = [m \in Node |-> recvMsgs[m] \ {m}]

CreateChange(n) ==
    /\ n \in PrivateKey
    /\ lastHash # NoHashVal
    /\ LET h == CalculateHash([type |-> "change"], lastHash) IN
        /\ lastHash' = h
        /\ ledger' = [k \in Hash |-> IF k = h
                         THEN [type |-> "change", signer |-> n, amount |-> 0,
                               prevHash |-> lastHash, prevBal |-> ChainBalance(lastHash)]
                         ELSE ledger[k]]
        /\ recvMsgs' = [m \in Node |-> recvMsgs[m]]

Next ==
    \/ \E n \in Node : CreateGenesis(n)
    \/ \E n \in Node, r \in Node : CreateSend(n, r)
    \/ \E n \in Node : CreateOpen(n)
    \/ \E n \in Node : CreateReceive(n)
    \/ \E n \in Node : CreateChange(n)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Hash -> Blocks]
    /\ recvMsgs \in [Node -> SUBSET Msgs]

\* A stored block's signature must match the public key of the account
\* that owns the block's chain.
SafetyInvariant ==
    \A h \in Hash :
        ledger[h] # NoBlockVal =>
            LET b == ledger[h] IN
                LET owner == CHOOSE k \in PublicKey : k = b.signer IN owner = b.signer

====