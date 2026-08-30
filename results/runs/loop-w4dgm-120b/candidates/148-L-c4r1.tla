---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(* Ed25519-style signatures over a Blake2b-style hash chain per account.  The
   spec tracks the last calculated hash, a replicated ledger per node, and a
   per-node received set of blocks awaiting validation.  Validation is what
   enforces the accounting discipline that the invariant relies on. *)

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

BlockType == {"genesis", "send", "open", "receive", "changeRep"}
Account == PublicKey
Block == [id: Hash, pkh: PublicKey, typ: BlockType, prev: Hash, link: Hash, amt: 0..GenesisBalance, sig: PrivateKey]
NoBlock == [id |-> NoBlockVal, pkh |-> NoHashVal, typ |-> "genesis", prev |-> NoHash, link |-> NoHash, amt |-> 0, sig |-> NoHashVal]

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET Block]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

OwnsChain(b) == b.pkh \in {Node[k] : k \in PrivateKey}

\* Balance walks the account chain backwards from the last hash; the chain is
\* finite because a block must reference an earlier chain position.
Balance(a, h) ==
    IF h = NoHash THEN 0
    ELSE IF ledger[a][h] # NoBlock /\ ledger[a][h].pkh = a
          THEN (IF ledger[a][h].typ = "receive" THEN ledger[a][h].amt ELSE 0) + Balance(a, ledger[a][h].prev)
          ELSE Balance(a, ledger[a][h].prev)

\* The sum of all account balances, derived from every account chain's blocks.
RECURSIVE SumBalances(_)
SumBalances(S) ==
    IF S = {} THEN 0
    ELSE LET a == CHOOSE e \in S : TRUE IN Balance(a, lastHash) + SumBalances(S \ {a})

\* The genesis block seeds the single shared chain and lands on every node.
CreateGenesisBlock(n, k) ==
    /\ lastHash = NoHash
    /\ \A c \in Node : lastHash \notin {ledger[c][h].id : h \in Hash}
    /\ \A h \in Hash : ledger[Node[n]][h] = NoBlock
    /\ lastHash' = CalculateHash([owner |-> n, amt |-> GenesisBalance])
    /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![lastHash] = [id |-> lastHash, pkh |-> n,
                                                                  typ |-> "genesis", prev |-> NoHash, link |-> NoHash,
                                                                  amt |-> GenesisBalance, sig |-> k]]]
    /\ received' = [received EXCEPT ![Node[n]] = @ \cup {[id |-> lastHash, pkh |-> n,
                                                        typ |-> "genesis", prev |-> NoHash, link |-> NoHash,
                                                        amt |-> GenesisBalance, sig |-> k]}]

CreateSendBlock(n, k, amt) ==
    /\ lastHash # NoHash
    /\ Balance(n, lastHash) >= amt
    /\ lastHash' = CalculateHash([owner |-> n, amt |-> amt])
    /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![lastHash] = [id |-> lastHash, pkh |-> n,
                                                                  typ |-> "send", prev |-> lastHash, link |-> NoHash,
                                                                  amt |-> amt, sig |-> k]]]
    /\ received' = [received EXCEPT ![Node[n]] = @ \cup {[id |-> lastHash, pkh |-> n,
                                                        typ |-> "send", prev |-> lastHash, link |-> NoHash,
                                                        amt |-> amt, sig |-> k]}]

CreateOpenBlock(n, k, sender) ==
    /\ lastHash # NoHash
    /\ \E b \in {r \in received[n] : r.typ = "send" /\ r.pkh = sender} :
        lastHash' = CalculateHash([owner |-> n, amt |-> b.amt])
    /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![lastHash] = [id |-> lastHash, pkh |-> n,
                                                                  typ |-> "open", prev |-> NoHash, link |-> b.id,
                                                                  amt |-> b.amt, sig |-> k]]]
    /\ received' = [received EXCEPT ![Node[n]] = @ \cup {[id |-> lastHash, pkh |-> n,
                                                        typ |-> "open", prev |-> NoHash, link |-> b.id,
                                                        amt |-> b.amt, sig |-> k]}]

CreateReceiveBlock(n, k, sender) ==
    /\ lastHash # NoHash
    /\ \E b \in {r \in received[n] : r.typ = "send" /\ r.pkh = sender} :
        lastHash' = CalculateHash([owner |-> n, amt |-> b.amt])
    /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![lastHash] = [id |-> lastHash, pkh |-> n,
                                                                  typ |-> "receive", prev |-> lastHash, link |-> b.id,
                                                                  amt |-> b.amt, sig |-> k]]]
    /\ received' = [received EXCEPT ![Node[n]] = @ \cup {[id |-> lastHash, pkh |-> n,
                                                        typ |-> "receive", prev |-> lastHash, link |-> b.id,
                                                        amt |-> b.amt, sig |-> k]}]

CreateChangeRepBlock(n, k) ==
    /\ lastHash # NoHash
    /\ lastHash' = CalculateHash([owner |-> n])
    /\ ledger' = [c \in Node |-> [ledger[c] EXCEPT ![lastHash] = [id |-> lastHash, pkh |-> n,
                                                                  typ |-> "changeRep", prev |-> lastHash, link |-> NoHash,
                                                                  amt |-> 0, sig |-> k]]]
    /\ received' = [received EXCEPT ![Node[n]] = @ \cup {[id |-> lastHash, pkh |-> n,
                                                        typ |-> "changeRep", prev |-> lastHash, link |-> NoHash,
                                                        amt |-> 0, sig |-> k]}]

\* Validation re-checks signatures and balance constraints against the local copy.
Validate(n, b) ==
    /\ b \in received[n]
    /\ OwnsChain(b)
    /\ ledger[n][b.id] = NoBlock
    /\ ledger[n][b.sig] # NoBlock
    /\ ledger[n][b.pkh] = NoBlock
    /\ LET pred == IF b.typ = "open" THEN NoHash ELSE b.prev IN
         IF pred = NoHash THEN TRUE
         ELSE ledger[n][pred] # NoBlock
    /\ \/ b.typ \in {"genesis", "changeRep"}
       \/ (b.typ = "send" /\ Balance(b.pkh, b.prev) >= b.amt)
       \/ (b.typ = "open" /\ ledger[n][b.link] # NoBlock /\ ledger[n][b.link].typ = "send")
       \/ (b.typ = "receive" /\ ledger[n][b.link] # NoBlock /\ ledger[n][b.link].typ = "send")
    /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![b.id] = b]]
    /\ received' = [received EXCEPT ![n] = @ \ {b}]
    /\ UNCHANGED lastHash

Next ==
    \/ \E n \in 1..Cardinality(Node), k \in PrivateKey : CreateGenesisBlock(n, k)
    \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance : CreateSendBlock(n, k, amt)
    \/ \E n \in Node, k \in PrivateKey, sender \in Node : CreateOpenBlock(n, k, sender)
    \/ \E n \in Node, k \in PrivateKey, sender \in Node : CreateReceiveBlock(n, k, sender)
    \/ \E n \in Node, k \in PrivateKey : CreateChangeRepBlock(n, k)
    \/ \E n \in Node, b \in Block : Validate(n, b)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A n \in Node, b \in Block : WF_vars(Validate(n, b))

\* Every block in every ledger copy is signed by the private key whose public
\* key names the account chain the block sits in.
SafetyInvariant ==
    \A c \in Node : \A h \in Hash :
        ledger[c][h] # NoBlock => ledger[c][h].sig \in {k \in PrivateKey : Node[k] = ledger[c][h].pkh}

\* The sum of all account balances must never exceed the genesis balance; it
\* is defined separately from the main safety invariant.
BalanceWithinGenesis == SumBalances(Node) <= GenesisBalance

====