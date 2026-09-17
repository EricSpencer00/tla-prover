;; Proof obligation:
;;	\A CONSTANT_f_ \in [Int -> Int] :
;;	   (\A CONSTANT_a_, CONSTANT_b_ \in Int :
;;	       CONSTANT_f_[2 * CONSTANT_a_] + 2 * CONSTANT_f_[CONSTANT_b_]
;;	       = CONSTANT_f_[CONSTANT_f_[CONSTANT_a_ + CONSTANT_b_]])
;;	   <=> (\A CONSTANT_z_ \in Int :
;;	           CONSTANT_f_[CONSTANT_z_] = 0
;;	           \/ (\E CONSTANT_c_ \in Int :
;;	                  \A CONSTANT_z__1 \in Int :
;;	                     CONSTANT_f_[CONSTANT_z__1]
;;	                     = 2 * CONSTANT_z__1 + CONSTANT_c_))
;; TLA+ Proof Manager 80172c6
;; Proof obligation #1
;; Generated from file "./imo_2019_p1.tla", line 8, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA____Cast__Int (Int) Idv)

(declare-fun smt__TLA____FunApp (Idv Idv) Idv)

(declare-fun smt__TLA____FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA____FunIsafcn (Idv) Bool)

(declare-fun smt__TLA____FunSet (Idv Idv) Idv)

(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)

(declare-fun smt__TLA____IntSet () Idv)

(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)

(declare-fun smt__TLA____Mem (Idv Idv) Bool)

(declare-fun smt__TLA____Proj__Int (Idv) Int)

(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (smt__TLA____Mem smt__z smt__x)
              (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y))
        :pattern ((smt__TLA____SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)
            (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g))
            (forall ((smt__x Idv))
              (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f))
                (= (smt__TLA____FunApp smt__f smt__x)
                  (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g))
        :pattern ((smt__TLA____FunIsafcn smt__f)
                   (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLA____FunIsafcn smt__f)
            (= (smt__TLA____FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLA____Mem smt__x smt__a)
                (smt__TLA____Mem (smt__TLA____FunApp smt__f smt__x) smt__b))))
          (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=> (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
          (and (smt__TLA____FunIsafcn smt__f)
            (= (smt__TLA____FunDom smt__f) smt__a)))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
            (smt__TLA____Mem smt__x smt__a))
          (smt__TLA____Mem (smt__TLA____FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
                   (smt__TLA____Mem smt__x smt__a))
        :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))
                   (smt__TLA____FunApp smt__f smt__x)))) :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((smt__x Int))
      (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x)))
        :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((smt__z Int))
      (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet)
        :pattern ((smt__TLA____Cast__Int smt__z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Int
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=> (smt__TLA____Mem smt__x smt__TLA____IntSet)
          (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x))))
        :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet))))
    :named |TypeGuardElim Int|))

;; Axiom: Typing TIntPlus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1)
            (smt__TLA____Cast__Int smt__x2))
          (smt__TLA____Cast__Int (+ smt__x1 smt__x2)))
        :pattern ((smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1)
                    (smt__TLA____Cast__Int smt__x2)))))
    :named |Typing TIntPlus|))

;; Axiom: Typing TIntTimes
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA____IntTimes (smt__TLA____Cast__Int smt__x1)
            (smt__TLA____Cast__Int smt__x2))
          (smt__TLA____Cast__Int (* smt__x1 smt__x2)))
        :pattern ((smt__TLA____IntTimes (smt__TLA____Cast__Int smt__x1)
                    (smt__TLA____Cast__Int smt__x2)))))
    :named |Typing TIntTimes|))

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

;; Goal
(assert
  (!
    (not
      (forall ((smt__CONSTANT__f__ Idv))
        (=>
          (smt__TLA____Mem smt__CONSTANT__f__
            (smt__TLA____FunSet smt__TLA____IntSet smt__TLA____IntSet))
          (=
            (forall ((smt__CONSTANT__a__ Idv) (smt__CONSTANT__b__ Idv))
              (=>
                (and (smt__TLA____Mem smt__CONSTANT__a__ smt__TLA____IntSet)
                  (smt__TLA____Mem smt__CONSTANT__b__ smt__TLA____IntSet))
                (=
                  (smt__TLA____IntPlus
                    (smt__TLA____FunApp smt__CONSTANT__f__
                      (smt__TLA____IntTimes (smt__TLA____Cast__Int 2)
                        smt__CONSTANT__a__))
                    (smt__TLA____IntTimes (smt__TLA____Cast__Int 2)
                      (smt__TLA____FunApp smt__CONSTANT__f__
                        smt__CONSTANT__b__)))
                  (smt__TLA____FunApp smt__CONSTANT__f__
                    (smt__TLA____FunApp smt__CONSTANT__f__
                      (smt__TLA____IntPlus smt__CONSTANT__a__
                        smt__CONSTANT__b__))))))
            (forall ((smt__CONSTANT__z__ Idv))
              (=> (smt__TLA____Mem smt__CONSTANT__z__ smt__TLA____IntSet)
                (or
                  (=
                    (smt__TLA____FunApp smt__CONSTANT__f__ smt__CONSTANT__z__)
                    (smt__TLA____Cast__Int 0))
                  (exists ((smt__CONSTANT__c__ Idv))
                    (and
                      (smt__TLA____Mem smt__CONSTANT__c__ smt__TLA____IntSet)
                      (forall ((smt__CONSTANT__z___1 Idv))
                        (=>
                          (smt__TLA____Mem smt__CONSTANT__z___1
                            smt__TLA____IntSet)
                          (=
                            (smt__TLA____FunApp smt__CONSTANT__f__
                              smt__CONSTANT__z___1)
                            (smt__TLA____IntPlus
                              (smt__TLA____IntTimes (smt__TLA____Cast__Int 2)
                                smt__CONSTANT__z___1) smt__CONSTANT__c__)))))))))))))
    :named |Goal|))

(check-sat)
(exit)
