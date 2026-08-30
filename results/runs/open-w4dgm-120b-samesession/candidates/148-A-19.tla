---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Every block in the block-lattice carries a single linear predecessor in its own
\* account chain, and the block's type plus its predecessor(s) is what fixes how
\* its amount is counted against the balance. That is why a block can only ever
\* be validated against a local ledger that already contains exactly the blocks
\* the block itself is expecting to see.
Accounts == PublicKey

\* A chain is a linked list of blocks; the recursive helper walks it to compute
\* the balance, which is the quantity the sending and receiving rules check.
RECURSIVE SumChain(_)
SumChain(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE x \in S : TRUE IN h.amount + SumChain(S \ {h})

Balance(n) == SumChain({ h \in NodeLedger[n] : h.chain = n })
TotalBalance == SumChain({ h \in UNION {NodeLedger[n] : n \in Node} : TRUE })

VARIABLES lastHash, nodeLedger, received

Blocks == [hash : Hash, prev : Hash \cup {NoHash}, type : {"genesis", "send", "open", "receive", "change"}, owner : Accounts, amount : Nat, recipient : Accounts]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ nodeLedger \in [Node -> SUBSET Blocks]
  /\ received \in [Node -> SUBSET Blocks]

Init ==
  /\ lastHash = NoHash
  /\ nodeLedger = [n \in Node |-> {}]
  /\ received = [n \in Node |-> {}]

CreateBlock(n, tp, amt, recp, prevH) ==
  /\ LET h == CalculateHash([tp |-> tp, owner |-> recp, amount |-> amt, prev |-> prevH])
     IN /\ h \notin UNION {NodeLedger[k] : k \in Node}
        /\ LET b == [hash |-> h, prev |-> prevH, type |-> tp, owner |-> recp, amount |-> amt, recipient |-> recp] IN
           /\ nodeLedger' = [k \in Node |-> nodeLedger[k] \cup {b}]
           /\ received' = [k \in Node |-> received[k] \cup {b}]
  /\ lastHash' = CalculateHash([tp |-> tp, owner |-> recp, amount |-> amt, prev |-> prevH])

\* Genesis block is the only block that needs no predecessor at all.
Genesis ==
  /\ \A n \in Node : \E b \in nodeLedger[n] : b.type = "genesis"
  /\ \A n \in Node : {b \in nodeLedger[n] : b.type = "genesis"} = {}
  /\ \E n \in Node, k \in PrivateKey :
       LET h == CalculateHash([tp |-> "genesis", owner |-> k, amount |-> GenesisBalance, prev |-> NoHash])
           b == [hash |-> h, prev |-> NoHash, type |-> "genesis", owner |-> k, amount |-> GenesisBalance, recipient |-> k]
       /\ nodeLedger' = [m \in Node |-> nodeLedger[m] \cup {b}]
       /\ received' = [m \in Node |-> received[m] \cup {b}]
       /\ lastHash' = h

ValidateSend(n, b) ==
  /\ b \in received[n]
  /\ b.type = "send"
  /\ b.owner \in Accounts
  /\ LET acctBal == Balance(b.owner), acctChain == {x \in nodeLedger[n] : x.chain = b.owner} IN
       /\ b.prev \in acctChain
       /\ b.amount <= acctBal
       /\ \A m \in Node : nodeLedger[m] = nodeLedger[n]
  /\ nodeLedger' = [k \in Node |-> nodeLedger[n]]
  /\ received' = [received EXCEPT ![n] = @ \ {b}]
  /\ UNCHANGED lastHash

ValidateOpen(n, b) ==
  /\ b \in received[n]
  /\ b.type = "open"
  /\ b.owner \in Accounts
  /\ LET acctBal == Balance(b.owner) IN
       /\ acctBal = 0
       /\ b.prev \in {x \in nodeLedger[n] : x.owner = b.recipient}
       /\ \A m \in Node : nodeLedger[m] = nodeLedger[n]
  /\ nodeLedger' = [k \in Node |-> nodeLedger[n]]
  /\ received' = [received EXCEPT ![n] = @ \ {b}]
  /\ UNCHANGED lastHash

ValidateReceive(n, b) ==
  /\ b \in received[n]
  /\ b.type = "receive"
  /\ b.owner \in Accounts
  /\ LET acctBal == Balance(b.owner), acctChain == {x \in nodeLedger[n] : x.chain = b.owner} IN
       /\ b.prev \in acctChain
       /\ b.recipient \in Accounts
       /\ \E m \in Node :
            /\ \E s \in nodeLedger[m] : s.type = "send" /\ s.hash = b.prev /\ s.recipient = b.owner
       /\ \A m \in Node : nodeLedger[m] = nodeLedger[n]
  /\ nodeLedger' = [k \in Node |-> nodeLedger[n]]
  /\ received' = [received EXCEPT ![n] = @ \ {b}]
  /\ UNCHANGED lastHash

ValidateChange(n, b) ==
  /\ b \in received[n]
  /\ b.type = "change"
  /\ b.owner \in Accounts
  /\ LET acctChain == {x \in nodeLedger[n] : x.chain = b.owner} IN
       /\ b.prev \in acctChain
       /\ \A m \in Node : nodeLedger[m] = nodeLedger[n]
  /\ nodeLedger' = [k \in Node |-> nodeLedger[n]]
  /\ received' = [received EXCEPT ![n] = @ \ {b}]
  /\ UNCHANGED lastHash

Next ==
  \/ Genesis
  \/ \E n \in Node, k \in PrivateKey : CreateBlock(n, "genesis", GenesisBalance, k, NoHash)
  \/ \E n \in Node, amt \in 1..GenesisBalance, recp \in Accounts, ph \in Hash \cup {NoHash} : CreateBlock(n, "send", amt, recp, ph)
  \/ \E n \in Node, amt \in 1..GenesisBalance, recp \in Accounts, ph \in Hash \cup {NoHash} : CreateBlock(n, "open", amt, recp, ph)
  \/ \E n \in Node, amt \in 1..GenesisBalance, recp \in Accounts, ph \in Hash \cup {NoHash} : CreateBlock(n, "receive", amt, recp, ph)
  \/ \E n \in Node, amt \in 0..GenesisBalance, recp \in Accounts, ph \in Hash \cup {NoHash} : CreateBlock(n, "change", amt, recp, ph)
  \/ \E n \in Node, b \in Blocks : ValidateSend(n, b)
  \/ \E n \in Node, b \in Blocks : ValidateOpen(n, b)
  \/ \E n \in Node, b \in Blocks : ValidateReceive(n, b)
  \/ \E n \in Node, b \in Blocks : ValidateChange(n, b)

Spec == Init /\ [][Next]_<<lastHash, nodeLedger, received>>

\* The signature check is the one thing that cannot be replaced by a structural
\* or chain-ordering check: it is the only reason a block placed by a malicious
\* node (or a compromised node's key) cannot still be accepted as the real
\* thing once the local ledger has otherwise caught up to it.
ValidSignature(b) == b.owner \in Accounts /\ b.hash = CalculateHash([tp |-> b.type, owner |-> b.owner, amount |-> b.amount, prev |-> b.prev])

SafetyInvariant == \A n \in Node : \A b \in nodeLedger[n] : ValidSignature(b)

====