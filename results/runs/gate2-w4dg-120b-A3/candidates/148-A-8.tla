---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* A Nano cryptocurrency block-lattice model. Hash and CalculateHash are
\* declared FREE so the .cfg can substitute concrete bounded versions.
\* The model tracks the last hash, a replicated per-node ledger of signed
\* blocks, and per-node received-but-unvalidated blocks.

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES
  lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Blocks are appended to the account's chain and their type governs the
\* balance arithmetic: send, open, receive, change-representative.
Types == [hash: Hash, owner: PublicKey, pred: {NoHash} \cup Hash,
          kind: {"send", "open", "receive", "change", "genesis"},
          amount: 0..GenesisBalance, sig: PrivateKey,
          recipient: PublicKey \cup {NoPublicKey}]

RECURSIVE ChainBalance(_)
ChainBalance(h) ==
  IF h = NoHash THEN 0
  ELSE LET b == ledger[Node][h] IN
       IF b.kind = "send" THEN ChainBalance(b.pred) - b.amount
       ELSE IF b.kind = "receive" THEN ChainBalance(b.pred) + b.amount
       ELSE ChainBalance(b.pred)

\* The sum of all account balances must never exceed the genesis balance.
\* It is not in the same invariant as the signature check.
RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET n == CHOOSE x \in S : TRUE IN SumBalances(S \ {n}) + ChainBalance(n)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Genesis block is a simultaneous commit to every node's ledger.
\* It can only fire while no block exists anywhere.
CreateGenesis(b, p) ==
  /\ \A n \in Node : \A h \in Hash : ledger[n][h] = NoBlockVal
  /\ b.kind = "genesis"
  /\ b.amount = GenesisBalance
  /\ ledger' = [n \in Node |-> [h \in Hash |->
        IF h = b.hash THEN [hash |-> b.hash, owner |-> p, pred |-> NoHash,
                             kind |-> b.kind, amount |-> b.amount,
                             sig |-> b.sig, recipient |-> NoPublicKey]
        ELSE NoBlockVal]]
  /\ lastHash' = b.hash
  /\ UNCHANGED received

CreateSend(n, b, p) ==
  /\ ChainBalance(n) >= b.amount
  /\ b.kind = "send"
  /\ b.pred = lastHash
  /\ ledger' = [ledger EXCEPT ![n][b.hash] =
        [hash |-> b.hash, owner |-> p, pred |-> b.pred, kind |-> b.kind,
         amount |-> b.amount, sig |-> b.sig, recipient |-> b.recipient]]
  /\ lastHash' = b.hash
  /\ received' = [r \in Node |-> received[r] \cup {b}]
  /\ UNCHANGED <<>>

CreateOpen(n, b, p) ==
  /\ b.kind = "open"
  /\ b.pred = NoHash
  /\ \A r \in received[n] : r.kind # "send" \/ r.recipient # p
  /\ ledger' = [ledger EXCEPT ![n][b.hash] =
        [hash |-> b.hash, owner |-> p, pred |-> b.pred, kind |-> b.kind,
         amount |-> b.amount, sig |-> b.sig, recipient |-> NoPublicKey]]
  /\ lastHash' = b.hash
  /\ received' = [received EXCEPT ![n] = @ \cup {b}]
  /\ UNCHANGED <<>>

CreateReceive(n, b, p) ==
  /\ b.kind = "receive"
  /\ b.pred \in Hash
  /\ \A r \in received[n] : r.kind # "send" \/ r.recipient # p
  /\ ledger' = [ledger EXCEPT ![n][b.hash] =
        [hash |-> b.hash, owner |-> p, pred |-> b.pred, kind |-> b.kind,
         amount |-> b.amount, sig |-> b.sig, recipient |-> NoPublicKey]]
  /\ lastHash' = b.hash
  /\ received' = [received EXCEPT ![n] = @ \cup {b}]
  /\ UNCHANGED <<>>

CreateChange(n, b, p) ==
  /\ b.kind = "change"
  /\ b.pred \in Hash
  /\ ledger' = [ledger EXCEPT ![n][b.hash] =
        [hash |-> b.hash, owner |-> p, pred |-> b.pred, kind |-> b.kind,
         amount |-> b.amount, sig |-> b.sig, recipient |-> NoPublicKey]]
  /\ lastHash' = b.hash
  /\ received' = [received EXCEPT ![n] = @ \cup {b}]
  /\ UNCHANGED <<>>

\* Validation checks the signature, the chain, and block-type rules.
Validate(n, h) ==
  /\ h \in received[n]
  /\ LET b == ledger[n][h] IN LET p == IF b.kind \in {"send", "open"} THEN b.recipient ELSE b.owner IN
       /\ b.sig = p
       /\ (b.kind = "send" => ledger[n][b.pred] # NoBlockVal /\ ChainBalance(n) >= b.amount)
       /\ (b.kind = "open" => ledger[n][b.pred] = NoBlockVal)
       /\ (b.kind = "receive" => ledger[n][b.pred] # NoBlockVal /\ ChainBalance(n) + b.amount <= GenesisBalance)
       /\ (b.kind = "change" => ledger[n][b.pred] # NoBlockVal)
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E b \in Types, p \in PublicKey : CreateGenesis(b, p)
  \/ \E n \in Node, b \in Types, p \in PublicKey : CreateSend(n, b, p)
  \/ \E n \in Node, b \in Types, p \in PublicKey : CreateOpen(n, b, p)
  \/ \E n \in Node, b \in Types, p \in PublicKey : CreateReceive(n, b, p)
  \/ \E n \in Node, b \in Types, p \in PublicKey : CreateChange(n, b, p)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in {NoHashVal} \cup Hash
  /\ ledger \in [Node -> [Hash -> Types \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Types]

SafetyInvariant ==
  /\ TypeInvariant
  /\ \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig = ledger[n][h].owner

====