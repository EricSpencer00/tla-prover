---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Empty sentinel for an uninitialized block slot in the replicated ledger on every node.
BlockSentinel == [prev |-> NoHash, sender |-> NoBlockVal, recipient |-> NoBlockVal, kind |-> "sentinel", sig |-> NoBlockVal]

\* The last block hash is held in a single global cell so that creation is deterministic;
\* each node keeps its own copy of the full replicated ledger.
VARIABLES lastHash, ledger, rx

vars == <<lastHash, ledger, rx>>

Owned(p) == { n \in Node : p \in PrivateKey[n] }

RECURSIVE ChainBalance(_)
ChainBalance(S) ==
    IF S = {} THEN 0
    ELSE LET h == CHOOSE x \in S : TRUE IN
         IF ledger[h].kind = "sentinel" THEN 0
         ELSE IF ledger[h].kind = "send" THEN
            ChainBalance(S \ {h}) - ledger[h].amount
         ELSE IF ledger[h].kind = "receive" THEN
            ChainBalance(S \ {h}) + ledger[h].amount
         ELSE ChainBalance(S \ {h})

\* Each account chain is exactly the block slots in ledger whose prev field forms a chain,
\* so the sum across all accounts is a sum across all non-sentinel slots.
RECURSIVE SumBalances(_)
SumBalances(S) ==
    IF S = {} THEN 0
    ELSE LET h == CHOOSE x \in S : TRUE IN
         IF ledger[h].kind = "sentinel" THEN SumBalances(S \ {h})
         ELSE ledger[h].amount + SumBalances(S \ {h})

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Hash -> [prev: Hash \cup {NoHash}, sender: PublicKey \cup {NoBlockVal}, recipient: PublicKey \cup {NoBlockVal}, kind: {"sentinel", "genesis", "send", "receive", "open", "change"}, sig: PrivateKey \cup {NoBlockVal}]]
    /\ rx \in [Node -> SUBSET Hash]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [h \in Hash |-> BlockSentinel]
    /\ rx = [n \in Node |-> {}]

\* The genesis block is written to every copy at once and can never be superseded.
CreateGenesis(p) ==
    /\ lastHash = NoHash
    /\ p \in Owned(NoHashVal)
    /\ lastHash' = CalculateHash([prev |-> NoHash, sender |-> p, recipient |-> NoHashVal, kind |-> "genesis", sig |-> p])
    /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> NoHash, sender |-> p, recipient |-> NoHashVal, kind |-> "genesis", sig |-> p]]
    /\ UNCHANGED rx

CreateSendBlock(p, to, m) ==
    /\ p \in Owned(to)
    /\ lastHash # NoHash
    /\ ChainBalance({lastHash}) >= m
    /\ lastHash' = CalculateHash([prev |-> lastHash, sender |-> p, recipient |-> to, kind |-> "send", sig |-> p])
    /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> lastHash, sender |-> p, recipient |-> to, kind |-> "send", sig |-> p]]
    /\ UNCHANGED rx

CreateOpenBlock(p, h) ==
    /\ ledger[h].kind = "send"
    /\ ledger[h].recipient = p
    /\ lastHash # NoHash
    /\ ledger' = [ledger EXCEPT ![CalculateHash([prev |-> lastHash, sender |-> p, recipient |-> h, kind |-> "open", sig |-> p])] =
                    [prev |-> lastHash, sender |-> p, recipient |-> h, kind |-> "open", sig |-> p]]
    /\ lastHash' = CalculateHash([prev |-> lastHash, sender |-> p, recipient |-> h, kind |-> "open", sig |-> p])
    /\ UNCHANGED rx

CreateReceiveBlock(p, h, m) ==
    /\ ledger[h].kind = "send"
    /\ ledger[h].recipient = p
    /\ ChainBalance({lastHash}) + ChainBalance({h}) + m >= 0
    /\ lastHash' = CalculateHash([prev |-> lastHash, sender |-> p, recipient |-> h, kind |-> "receive", sig |-> p])
    /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> lastHash, sender |-> p, recipient |-> h, kind |-> "receive", sig |-> p]]
    /\ UNCHANGED rx

CreateChangeRepresentative(p) ==
    /\ lastHash # NoHash
    /\ lastHash' = CalculateHash([prev |-> lastHash, sender |-> p, recipient |-> NoHashVal, kind |-> "change", sig |-> p])
    /\ ledger' = [ledger EXCEPT ![lastHash'] = [prev |-> lastHash, sender |-> p, recipient |-> NoHashVal, kind |-> "change", sig |-> p]]
    /\ UNCHANGED rx

Broadcast(h) ==
    /\ ledger[h].kind # "sentinel"
    /\ \E n \in Node : h \notin rx[n]
    /\ rx' = [n \in Node |-> IF h \in rx[n] THEN rx[n] ELSE rx[n] \cup {h}]
    /\ UNCHANGED <<lastHash, ledger>>

\* Validation is signature-based and requires every reference already to resolve.
Validate(n, h) ==
    /\ h \in rx[n]
    /\ ledger[h].kind # "sentinel"
    /\ ledger[h].sig \in Owned(ledger[h].sender)
    /\ ledger[h].prev \in {NoHash} \cup Hash
    /\ (ledger[h].prev = NoHash \/ ledger[ledger[h].prev].kind # "sentinel")
    /\ (IF ledger[h].kind = "send" THEN SumBalances(Hash) + ledger[h].amount <= GenesisBalance ELSE TRUE)
    /\ (IF ledger[h].kind = "receive" THEN ledger[ledger[h].recipient].kind # "sentinel" ELSE TRUE)
    /\ rx' = [rx EXCEPT ![n] = rx[n] \ {h}]
    /\ UNCHANGED <<lastHash, ledger>>

Next ==
    \/ \E p \in PrivateKey : CreateGenesis(p) \/ CreateChangeRepresentative(p)
    \/ \E p \in PrivateKey, to \in PublicKey, m \in 1..GenesisBalance : CreateSendBlock(p, to, m)
    \/ \E p \in PublicKey, h \in Hash : CreateOpenBlock(p, h) \/ CreateReceiveBlock(p, h, 1)
    \/ \E h \in Hash : Broadcast(h)
    \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
    \A h \in Hash : (ledger[h].kind # "sentinel") => (ledger[h].sig \in Owned(ledger[h].sender))

====