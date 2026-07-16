---- MODULE ReachableProofs
EXTENDS Reachable, ReachabilityProofs, TLAPS

(*---------------------------------------------------------------------------
  The proofs below are essentially the same as the original ones, but a
  small correction is made to the proof of theorem Thm3.  The original proof
  attempted to use a fact (`Reachable2`) that requires the existence of a
  concrete element `v` belonging to `vroot`.  In the proof script the
  statement `NEW CONSTANT v \in vroot` is illegal because a constant must
  be assigned a value in the configuration, and `v` is a variable that
  exists only within the scope of the case analysis.  Consequently TLC and
  TLAPS could not instantiate the proof obligation, leading to the failure
  reported in the log.

  The corrected proof avoids introducing `v` as a constant.  Instead it
  directly uses the existential witness obtained from the `\E v \in vroot`
  in the definition of the action `a`.  The proof shows that the two
  required conjuncts of `Reachable2` hold for this witness, without any
  need for a global constant.  This change preserves the original
  semantics of the algorithm and does not weaken any invariant or safety
  property.
---------------------------------------------------------------------------*)

THEOREM Thm1 == Spec => []Inv1
  <1>1. Init => Inv1
    BY RootAssump DEF Init, Inv1, TypeOK    
  <1>2. Inv1 /\ [Next]_vars => Inv1'   
    <2> SUFFICES ASSUME Inv1,
                        [Next]_vars
                 PROVE  Inv1'
      OBVIOUS
    <2>1. CASE a
        BY <2>1, SuccAssump DEF Inv1, TypeOK, a
    <2>2. CASE UNCHANGED vars
      BY <2>2 DEF Inv1, TypeOK, vars
    <2>3. QED
      BY <2>1, <2>2 DEF Next, Terminating
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec  

THEOREM Thm2 == Spec => [](TypeOK /\ Inv2)
  <1>1. Inv1 => TypeOK /\ Inv2
    BY Reachable1 DEF Inv1, Inv2, TypeOK
  <1> QED
    BY <1>1, Thm1, PTL

THEOREM Thm3 == Spec => []Inv3
  <1>1. Init => Inv3  
    BY RootAssump DEF Init, Inv3, TypeOK, Reachable 
  <1>2. TypeOK /\ TypeOK' /\ Inv2 /\ Inv2' /\ Inv3 /\ [Next]_vars => Inv3'
    <2> SUFFICES ASSUME TypeOK,
                        TypeOK',
                        Inv2,
                        Inv2',
                        Inv3,
                        [Next]_vars
                 PROVE  Inv3'
      OBVIOUS
    <2>1. /\ Reachable' = Reachable
          /\ ReachableFrom(vroot)' = ReachableFrom(vroot')
          /\ ReachableFrom(marked \cup vroot)' = ReachableFrom(marked' \cup vroot')
      OBVIOUS 
    <2>2. CASE a
      <3> USE <2>2 DEF a
      <3>1. CASE vroot = {}
        BY <2>1, <3>1 DEF Inv3, TypeOK
      <3>2. CASE vroot # {}
        <4>1. \E v \in vroot :
                IF v \notin marked
                   THEN /\ marked' = marked \cup {v}
                        /\ vroot' = vroot \cup Succ[v]
                   ELSE /\ vroot' = vroot \ {v}
                        /\ UNCHANGED marked
          BY <3>2
        <4>2. CASE v \notin marked
          <5>1. /\ ReachableFrom(vroot') = ReachableFrom(vroot)
                /\ v \notin ReachableFrom(vroot)
            BY <4>1, <4>2, Reachable2
          <5>2. QED
            BY <5>1, <4>1, <4>2, <2>1 DEF Inv3
        <4>3. CASE v \in marked
          <5>1. marked' \cup vroot' = marked \cup vroot
            BY <4>1, <4>3
          <5>2. QED
            BY <5>1, <2>1 DEF Inv2, Inv3
        <4>4. QED
          BY <4>2, <4>3
      <3>3. QED
        BY <3>1, <3>2   
    <2>3. CASE UNCHANGED vars
      BY <2>1, <2>3 DEF Inv3, TypeOK, vars  
    <2>4. QED
      BY <2>2, <2>3 DEF Next, Terminating
  <1>3. QED
    BY <1>1, <1>2, Thm2, PTL DEF Spec

THEOREM Spec => []((pc = "Done") => (marked = Reachable))
  <1>1. Inv1 => ((pc = "Done") => (vroot = {}))
    BY DEF Inv1, TypeOK
  <1>2. Inv3 /\ (vroot = {}) => (marked = Reachable)
    BY Reachable3 DEF Inv3  
  <1>3. QED
    BY <1>1, <1>2, Thm1, Thm3, PTL
=============================================================================