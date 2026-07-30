---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS
    Hash,
    NoHashVal,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance,
    NoBlockVal,
    CalculateHash,
    NoHash,
    NoBlock

\* The original Nano blockchain modelled here has every account as its own chain, and
\* every block contains a cryptographic hash that depends on the previous block's hash.
\* The model tracks: (1) the last calculated block hash, (2) the replicated ledger
\* (one per node), and (3) received-but-unvalidated blocks for each node.

Block == [typ : {"genesis", "send", "open", "receive", "change"},
          self : Hash,
          account : PublicKey,
          prev : Hash,
          recipient : PublicKey,
          amount : 0..GenesisBalance,
          signer : PrivateKey]

RECURSIVE ChainBalance(_, _)
ChainBalance(b, h) ==
    IF h = NoHash
        THEN 0
        ELSE LET w == ChainBalance(b, b[h].prev) IN
             IF b[h].typ = "send" THEN w - b[h].amount
             ELSE IF b[h].typ = "open" THEN b[h].amount
             ELSE IF b[h].typ = "receive" THEN w + b[h].amount
             ELSE w

RECURSIVE BalanceHeld(_, _)
BalanceHeld(b, k) ==
    IF k = 0
        THEN 0
        ELSE LET h == b[k] IN
             IF b[h].typ = "receive" THEN b[h].amount + BalanceHeld(b, k - 1) ELSE BalanceHeld(b, k - 1)

RECURSIVE TotalBalance(_)
TotalBalance(m) ==
    IF m = 0
        THEN 0
        ELSE BalanceHeld(m, m) + TotalBalance(m - 1)

Nodes == 1..Node
Keys == 1..PublicKey

TypeInvariant ==
    /\ LastHash \in Hash \cup {NoHash}
    /\ Ledger \in [Nodes -> [Hash -> Block \cup {NoBlock}]]
    /\ Received \in [Nodes -> SUBSET Hash]

\* Every block in every node's ledger must have a signature matching the account's
\* public key; this is the only cryptographic property the model tracks.
SafetyInvariant ==
    \A n \in Nodes : \A h \in Hash : Ledger[n][h] # NoBlock => Ledger[n][h].signer = h

Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Nodes |-> [h \in Hash |-> NoBlock]]
    /\ Received = [n \in Nodes |-> {}]

\* Create the genesis block, adding it to all nodes' ledgers at once.
CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E k \in PrivateKey :
        \E h \in Hash :
            /\ Ledger' = [n \in Nodes |-> [Ledger[n] EXCEPT ![h] =
                        [typ |-> "genesis", self |-> h, account |-> k,
                         prev |-> NoHash, recipient |-> 0, amount |-> GenesisBalance,
                         signer |-> k]]]
            /\ LastHash' = h
    /\ UNCHANGED Received

\* A send block debits the sender's balance.
CreateSend ==
    /\ LastHash # NoHash
    /\ \E k \in PrivateKey :
        \E h \in Hash :
            /\ Ledger' = [n \in Nodes |-> [Ledger[n] EXCEPT ![h] =
                        [typ |-> "send", self |-> h, account |-> k,
                         prev |-> LastHash, recipient |-> NoHashVal, amount |-> 1,
                         signer |-> k]]]
            /\ LastHash' = h
    /\ Received' = [n \in Nodes |-> Received[n] \cup {h}]

CreateOpen ==
    /\ LastHash # NoHash
    /\ \E k \in PrivateKey :
        \E h \in Hash :
            /\ Ledger' = [n \in Nodes |-> [Ledger[n] EXCEPT ![h] =
                        [typ |-> "open", self |-> h, account |-> k,
                         prev |-> LastHash, recipient |-> 0, amount |-> 1,
                         signer |-> k]]]
            /\ LastHash' = h
    /\ Received' = [n \in Nodes |-> Received[n] \cup {h}]

CreateReceive ==
    /\ LastHash # NoHash
    /\ \E k \in PrivateKey :
        \E h \in Hash :
            /\ Ledger' = [n \in Nodes |-> [Ledger[n] EXCEPT ![h] =
                        [typ |-> "receive", self |-> h, account |-> k,
                         prev |-> LastHash, recipient |-> NoHashVal, amount |-> 1,
                         signer |-> k]]]
            /\ LastHash' = h
    /\ Received' = [n \in Nodes |-> Received[n] \cup {h}]

CreateChange ==
    /\ LastHash # NoHash
    /\ \E k \in PrivateKey :
        \E h \in Hash :
            /\ Ledger' = [n \in Nodes |-> [Ledger[n] EXCEPT ![h] =
                        [typ |-> "change", self |-> h, account |-> k,
                         prev |-> LastHash, recipient |-> 0, amount |-> 0,
                         signer |-> k]]]
            /\ LastHash' = h
    /\ Received' = [n \in Nodes |-> Received[n] \cup {h}]

ValidateBlock ==
    /\ \E n \in Nodes :
        /\ \E h \in Received[n] :
            /\ Ledger' = [Ledger EXCEPT ![n][h] = Ledger[CHOOSE m \in Nodes : TRUE][h]]
            /\ Received' = [Received EXCEPT ![n] = @ \ {h}]
    /\ UNCHANGED LastHash

Next == CreateGenesis \/ CreateSend \/ CreateOpen \/ CreateReceive \/ CreateChange \/ ValidateBlock

Spec == Init /\ [][Next]_<<LastHash, Ledger, Received>>

====