---
title: Simpson's delooping of the sign homomorphism
---

```agda
{-# OPTIONS --without-K --experimental-lossy-unification #-}

module finite-group-theory.simpson-delooping-sign-homomorphism where

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import finite-group-theory.delooping-sign-homomorphism
open import finite-group-theory.finite-type-groups
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions

open import foundation.commuting-squares
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equivalence-relations
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-set-quotients
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.truncated-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import group-theory.automorphism-groups
open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-generated-subgroups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets
open import group-theory.semigroups
open import group-theory.subgroups-generated-by-subsets-groups
open import group-theory.symmetric-groups

open import synthetic-homotopy-theory.loop-spaces

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.lists
open import univalent-combinatorics.standard-finite-types
```

### Simpson's delooping of the sign homomorphism

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin l n)
  where

  sign-comp-Eq-Rel : Eq-Rel lzero (Fin n ≃ type-UU-Fin n X)
  pr1 sign-comp-Eq-Rel f g =
    Id-Prop (Fin-Set 2) (zero-Fin 1) (sign-homomorphism-Fin-two n X (f ∘e inv-equiv g))
  pr1 (pr2 sign-comp-Eq-Rel) {f} =
    ap pr1
      { x = pair (zero-Fin 1) (unit-trunc-Prop (pair nil (pair refl (right-inverse-law-equiv f))))}
      { y = center (is-contr-parity-transposition-permutation n X (f ∘e inv-equiv f))}
      ( eq-is-contr (is-contr-parity-transposition-permutation n X (f ∘e inv-equiv f)))
  pr1 (pr2 (pr2 sign-comp-Eq-Rel)) {f} {g} P =
    ap pr1
      { x = pair (zero-Fin 1) (unit-trunc-Prop (pair nil (pair refl (left-inverse-law-equiv (f ∘e inv-equiv g)))))}
      { y = center (is-contr-parity-transposition-permutation n X (inv-equiv (f ∘e inv-equiv g) ∘e (f ∘e inv-equiv g)))}
      ( eq-is-contr
        ( is-contr-parity-transposition-permutation n X
          ( inv-equiv (f ∘e inv-equiv g) ∘e (f ∘e inv-equiv g)))) ∙
      ( ( preserves-add-sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)) (f ∘e inv-equiv g)) ∙
        ( ( ap
          ( add-Fin 2 (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g))))
          ( inv P)) ∙
          ( ( ap
            ( λ k →
              mod-two-ℕ (add-ℕ (nat-Fin 2 (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)))) k))
            ( is-zero-nat-zero-Fin {k = 1})) ∙
            ( ( issec-nat-Fin 1 (sign-homomorphism-Fin-two n X (inv-equiv (f ∘e inv-equiv g)))) ∙
              ( ap
                ( sign-homomorphism-Fin-two n X)
                ( ( distributive-inv-comp-equiv (inv-equiv g) f) ∙
                  ap (λ h → h ∘e inv-equiv f) (inv-inv-equiv g)))))))
  pr2 (pr2 (pr2 sign-comp-Eq-Rel)) {f} {g} {h} P Q =
    ( ap mod-two-ℕ
      ( ( ap (add-ℕ zero-ℕ) (inv (is-zero-nat-zero-Fin {k = 1}) ∙ ap (nat-Fin 2) Q)) ∙
        ( ap
          ( λ k → add-ℕ k (nat-Fin 2 (sign-homomorphism-Fin-two n X (g ∘e inv-equiv h))))
          ( inv (is-zero-nat-zero-Fin {k = 1}) ∙ ap (nat-Fin 2) P)))) ∙
      ( ( inv
        ( preserves-add-sign-homomorphism-Fin-two n X (f ∘e inv-equiv g) (g ∘e inv-equiv h))) ∙
        ( ap
          ( sign-homomorphism-Fin-two n X)
          ( ( associative-comp-equiv (g ∘e inv-equiv h) (inv-equiv g) f) ∙
            ( ap
              ( λ h' → f ∘e h')
              ( ( inv (associative-comp-equiv (inv-equiv h) g (inv-equiv g))) ∙
                ( ( ap (λ h' → h' ∘e inv-equiv h) (left-inverse-law-equiv g)) ∙
                  ( left-unit-law-equiv (inv-equiv h))))))))

  is-decidable-sign-comp-Eq-Rel : (f g : Fin n ≃ type-UU-Fin n X) →
    is-decidable (sim-Eq-Rel sign-comp-Eq-Rel f g)
  is-decidable-sign-comp-Eq-Rel f g =
    has-decidable-equality-is-finite
      ( is-finite-Fin 2)
      ( zero-Fin 1)
      ( sign-homomorphism-Fin-two n X (f ∘e inv-equiv g))

  quotient-sign-comp : UU (lsuc lzero ⊔ l)
  quotient-sign-comp = equivalence-class sign-comp-Eq-Rel

  quotient-sign-comp-Set : Set (lsuc lzero ⊔ l)
  quotient-sign-comp-Set = equivalence-class-Set sign-comp-Eq-Rel

module _
  {l : Level} {X : UU l} (eX : count X) (ineq : leq-ℕ 2 (number-of-elements-count eX))
  where

  private abstract
    lemma :
      Id
        ( inr star)
        ( sign-homomorphism-Fin-two
          ( number-of-elements-count eX)
          ( X , unit-trunc-Prop (equiv-count eX))
          ( equiv-count eX ∘e
            inv-equiv
              (equiv-count eX ∘e
                transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin (number-of-elements-count eX))
                    ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))
    lemma =
      ( inv
        ( eq-sign-homomorphism-Fin-two-transposition
          ( number-of-elements-count eX)
          ( Fin (number-of-elements-count eX) , (unit-trunc-Prop id-equiv))
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-Fin (number-of-elements-count eX))
            ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))) ∙
        ( ( inv
          ( preserves-conjugation-sign-homomorphism-Fin-two
            ( number-of-elements-count eX)
            ( Fin (pr1 eX) , unit-trunc-Prop id-equiv)
            ( X , (unit-trunc-Prop (equiv-count eX)))
            ( transposition
              ( standard-2-Element-Decidable-Subtype
                ( has-decidable-equality-Fin (pr1 eX))
                ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (pr1 eX) ineq)))))
            ( equiv-count eX))) ∙
          ( ap
            ( λ h →
              sign-homomorphism-Fin-two
                ( number-of-elements-count eX)
                ( X , unit-trunc-Prop (equiv-count eX))
                ( equiv-count eX ∘e h))
            ( ( ap (λ h → h ∘e inv-equiv (equiv-count eX))
              ( inv
                ( own-inverse-is-involution
                  ( is-involution-map-transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-Fin (number-of-elements-count eX))
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (pr1 eX) ineq)))))))) ∙
              ( inv
                ( distributive-inv-comp-equiv
                  ( transposition
                    ( standard-2-Element-Decidable-Subtype
                      ( has-decidable-equality-Fin (number-of-elements-count eX))
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
                  ( equiv-count eX))))))

  not-sign-comp-transposition-count :
    (Y : 2-Element-Decidable-Subtype l X) →
    ¬ ( sim-Eq-Rel
      ( sign-comp-Eq-Rel
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX))))
      ( transposition Y ∘e equiv-count eX)
      ( transposition Y ∘e (transposition Y ∘e equiv-count eX)))
  not-sign-comp-transposition-count Y P =
    neq-inl-inr
      ( P ∙
        ( ( ap
          ( sign-homomorphism-Fin-two
            ( number-of-elements-count eX)
            ( X , unit-trunc-Prop (equiv-count eX)))
          ( ( ap
            ( λ h → ((transposition Y ∘e equiv-count eX) ∘e h))
            ( distributive-inv-comp-equiv
              ( transposition Y ∘e equiv-count eX)
              ( transposition Y))) ∙
            ( ( compose-equiv-compose-inv-equiv
              ( transposition Y ∘e equiv-count eX)
              ( inv-equiv (transposition Y))) ∙
              ( own-inverse-is-involution
                ( is-involution-map-transposition Y))))) ∙
          ( eq-sign-homomorphism-Fin-two-transposition
            ( number-of-elements-count eX)
            ( X , unit-trunc-Prop (equiv-count eX))
            ( Y))))

  inv-Fin-2-quotient-sign-comp-count :
    ( T : quotient-sign-comp (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))) →
    is-decidable
      ( is-in-equivalence-class
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX)) →
    Fin 2
  inv-Fin-2-quotient-sign-comp-count T (inl P) = inl (inr star)
  inv-Fin-2-quotient-sign-comp-count T (inr NP) = inr star

  equiv-Fin-2-quotient-sign-comp-count : Fin 2 ≃
    quotient-sign-comp (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
  pr1 equiv-Fin-2-quotient-sign-comp-count (inl (inr star)) =
    class
      ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
      ( equiv-count eX)
  pr1 equiv-Fin-2-quotient-sign-comp-count (inr star) =
    class
      ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
      ( equiv-count eX ∘e
        transposition
          ( standard-2-Element-Decidable-Subtype
            ( has-decidable-equality-Fin (number-of-elements-count eX))
            ( pr2 (pr2 ( two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
  pr2 equiv-Fin-2-quotient-sign-comp-count =
    is-equiv-has-inverse
      (λ T →
        inv-Fin-2-quotient-sign-comp-count T
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))) (a ∘e inv-equiv b)))
            ( T)
            ( equiv-count eX)))
      ( λ T →
        retr-Fin-2-quotient-sign-comp-count T
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))) (a ∘e inv-equiv b)))
            ( T)
            ( equiv-count eX)))
      ( λ k →
        sec-Fin-2-quotient-sign-comp-count k
          ( is-decidable-is-in-equivalence-class-is-decidable
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( λ a b →
              has-decidable-equality-Fin 2
                ( zero-Fin 1)
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))) (a ∘e inv-equiv b)))
            ( pr1 equiv-Fin-2-quotient-sign-comp-count k)
            ( equiv-count eX)))
    where
    cases-retr-Fin-2-quotient-sign-comp-count :
      ( T : quotient-sign-comp
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))) →
      ¬ ( is-in-equivalence-class
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX)) →
      ( f : Fin (number-of-elements-count eX) ≃ X) →
      Id
        ( class
          ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
          ( f))
        ( T) →
      ( k : Fin 2) →
      Id
        ( k)
        ( sign-homomorphism-Fin-two
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( f ∘e inv-equiv (equiv-count eX))) →
      is-in-equivalence-class
        ( sign-comp-Eq-Rel
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))))
        ( T)
        ( equiv-count eX ∘e
          transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-Fin
                (number-of-elements-count eX))
              ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))    
    cases-retr-Fin-2-quotient-sign-comp-count T NP f p (inl (inr star)) q =
      ex-falso
        ( NP
          ( tr
            ( λ x →
              is-in-equivalence-class
                ( sign-comp-Eq-Rel
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))))
                ( x)
                ( equiv-count eX))
            ( p)
            ( q)))
    cases-retr-Fin-2-quotient-sign-comp-count T NP f p (inr star) q =
      tr
        ( λ x →
          is-in-equivalence-class
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))
            ( x)
            ( equiv-count eX ∘e
              transposition
                ( standard-2-Element-Decidable-Subtype
                  ( has-decidable-equality-Fin
                    (number-of-elements-count eX))
                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
        ( p)
        ( ( eq-mod-succ-cong-ℕ 1 0 2 (cong-zero-ℕ' 2)) ∙
          ( ( ap-add-Fin 2
            ( q)
            ( lemma)) ∙
            ( ( inv
              ( preserves-add-sign-homomorphism-Fin-two
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( f ∘e inv-equiv (equiv-count eX))
                ( equiv-count eX ∘e
                  inv-equiv
                    ( equiv-count eX ∘e
                      transposition
                        ( standard-2-Element-Decidable-Subtype
                          ( has-decidable-equality-Fin
                            ( number-of-elements-count eX))
                            ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))) ∙
               ap
                ( sign-homomorphism-Fin-two
                  ( number-of-elements-count eX)
                  ( pair X (unit-trunc-Prop (equiv-count eX))))
                ( ( associative-comp-equiv
                  ( equiv-count eX ∘e
                    inv-equiv
                      ( equiv-count eX ∘e
                        transposition
                          ( standard-2-Element-Decidable-Subtype
                            (has-decidable-equality-Fin (number-of-elements-count eX))
                            ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                  ( inv-equiv (equiv-count eX))
                  ( f)) ∙
                  ( ap
                    ( λ h → f ∘e h)
                    ( inv
                      ( associative-comp-equiv
                        ( inv-equiv
                          ( equiv-count eX ∘e
                            transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin (number-of-elements-count eX))
                              ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                        ( equiv-count eX)
                        ( inv-equiv (equiv-count eX))) ∙
                      ( ( ap
                        ( λ h →
                          h ∘e
                            inv-equiv
                              ( equiv-count eX ∘e
                                transposition
                                  ( standard-2-Element-Decidable-Subtype
                                    ( has-decidable-equality-Fin (number-of-elements-count eX))
                                    (pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
                        ( left-inverse-law-equiv (equiv-count eX))) ∙
                        ( left-unit-law-equiv
                          ( inv-equiv
                            ( equiv-count eX ∘e
                              transposition
                                ( standard-2-Element-Decidable-Subtype
                                  ( has-decidable-equality-Fin (number-of-elements-count eX))
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))))))))))
    retr-Fin-2-quotient-sign-comp-count :
      ( T : quotient-sign-comp
        ( number-of-elements-count eX)
        ( pair X (unit-trunc-Prop (equiv-count eX)))) →
      ( H : is-decidable
        (is-in-equivalence-class
          ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
          ( T)
          ( equiv-count eX))) →
      Id
        ( pr1 equiv-Fin-2-quotient-sign-comp-count (inv-Fin-2-quotient-sign-comp-count T H))
        ( T)
    retr-Fin-2-quotient-sign-comp-count T (inl P) =
      eq-effective-quotient'
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( equiv-count eX)
        ( T)
        ( P)
    retr-Fin-2-quotient-sign-comp-count T (inr NP) =
      eq-effective-quotient'
        ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( equiv-count eX ∘e
          transposition
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-Fin
                ( number-of-elements-count eX))
                ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
        ( T)
        ( apply-universal-property-trunc-Prop
          ( pr2 T)
          ( pair
            ( is-in-equivalence-class
              ( sign-comp-Eq-Rel
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( equiv-count eX ∘e
                transposition
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin
                      ( number-of-elements-count eX))
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))))
            ( is-prop-is-in-equivalence-class
              ( sign-comp-Eq-Rel
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX))))
              ( T)
              ( equiv-count eX ∘e
                transposition
                  (standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin
                      ( number-of-elements-count eX))
                      ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))
          ( λ (pair t p) →
            cases-retr-Fin-2-quotient-sign-comp-count T NP t
              ( inv
                ( eq-has-same-elements-equivalence-class
                  ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
                  ( T)
                  ( class
                    ( sign-comp-Eq-Rel (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
                    ( t))
                  ( p)))
              ( sign-homomorphism-Fin-two
                ( number-of-elements-count eX)
                ( pair X (unit-trunc-Prop (equiv-count eX)))
                ( t ∘e inv-equiv (equiv-count eX)))
              ( refl)))
    sec-Fin-2-quotient-sign-comp-count : (k : Fin 2) →
      ( D : is-decidable
        ( is-in-equivalence-class
          ( sign-comp-Eq-Rel
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))))
          ( pr1 equiv-Fin-2-quotient-sign-comp-count k)
          ( equiv-count eX))) →
      Id
        ( inv-Fin-2-quotient-sign-comp-count
          ( pr1 equiv-Fin-2-quotient-sign-comp-count k)
          ( D))
        ( k)
    sec-Fin-2-quotient-sign-comp-count (inl (inr star)) (inl D) = refl
    sec-Fin-2-quotient-sign-comp-count (inl (inr star)) (inr ND) =
      ex-falso
        ( ND
          ( refl-Eq-Rel
            ( sign-comp-Eq-Rel
              ( number-of-elements-count eX)
              ( pair X (unit-trunc-Prop (equiv-count eX))))))
    sec-Fin-2-quotient-sign-comp-count (inr star) (inl D) =
      ex-falso
        ( neq-inr-inl
          (lemma ∙
            ( inv
              ( D ∙
                 ap
                  ( sign-homomorphism-Fin-two
                    ( number-of-elements-count eX)
                    ( pair X (unit-trunc-Prop (equiv-count eX))))
                  ( ( associative-comp-equiv
                    ( inv-equiv (equiv-count eX))
                    ( transposition
                      ( standard-2-Element-Decidable-Subtype
                        ( has-decidable-equality-Fin (number-of-elements-count eX))
                        ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
                    ( equiv-count eX)) ∙
                    ( ap
                      ( λ h → equiv-count eX ∘e h)
                      ( ( ap
                        ( λ h → h ∘e inv-equiv (equiv-count eX))
                        { x =
                          transposition
                            (standard-2-Element-Decidable-Subtype
                              ( has-decidable-equality-Fin
                                ( number-of-elements-count eX))
                                ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq))))}
                        ( inv
                          ( own-inverse-is-involution
                            ( is-involution-map-transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin
                                  ( number-of-elements-count eX))
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))))) ∙
                        ( inv
                          ( distributive-inv-comp-equiv
                            ( transposition
                              ( standard-2-Element-Decidable-Subtype
                                ( has-decidable-equality-Fin
                                  ( number-of-elements-count eX))
                                  ( pr2 (pr2 (two-distinct-elements-leq-2-Fin (number-of-elements-count eX) ineq)))))
                            ( equiv-count eX))))))))))
    sec-Fin-2-quotient-sign-comp-count (inr star) (inr ND) = refl

module _
  {l : Level} (n : ℕ) (X : UU-Fin l n) (ineq : leq-ℕ 2 n)
  where
  
  equiv-fin-2-quotient-sign-comp-equiv-Fin : (h : Fin n ≃ type-UU-Fin n X) →
    ( Fin 2 ≃ quotient-sign-comp n X)
  equiv-fin-2-quotient-sign-comp-equiv-Fin h =
    tr
      ( λ e → Fin 2 ≃ quotient-sign-comp n (pair (type-UU-Fin n X) e))
      ( all-elements-equal-type-trunc-Prop (unit-trunc-Prop (equiv-count (pair n h))) (pr2 X))
      ( equiv-Fin-2-quotient-sign-comp-count (pair n h) ineq)
```

```agda
module _
  {l : Level} (n : ℕ)
  where

  map-simpson-comp-equiv : (X X' : UU-Fin l n) →
    (type-UU-Fin n X ≃ type-UU-Fin n X') → (Fin n ≃ type-UU-Fin n X) →
    (Fin n ≃ type-UU-Fin n X')
  map-simpson-comp-equiv X X' e f = e ∘e f

  simpson-comp-equiv : (X X' : UU-Fin l n) →
    (type-UU-Fin n X ≃ type-UU-Fin n X') →
    (Fin n ≃ type-UU-Fin n X) ≃ (Fin n ≃ type-UU-Fin n X')
  pr1 (simpson-comp-equiv X X' e) = map-simpson-comp-equiv X X' e
  pr2 (simpson-comp-equiv X X' e) =
    is-equiv-has-inverse
      ( map-simpson-comp-equiv X' X (inv-equiv e))
      ( λ f →
        ( inv (associative-comp-equiv f (inv-equiv e) e)) ∙
          ( ap (λ h → h ∘e f) (right-inverse-law-equiv e) ∙ left-unit-law-equiv f))
      ( λ f →
        ( inv (associative-comp-equiv f e (inv-equiv e))) ∙
          ( ap (λ h → h ∘e f) (left-inverse-law-equiv e) ∙ left-unit-law-equiv f))

  abstract
    preserves-id-equiv-simpson-comp-equiv : (X : UU-Fin l n) →
      Id (simpson-comp-equiv X X id-equiv) id-equiv
    preserves-id-equiv-simpson-comp-equiv X =
      eq-htpy-equiv (λ f → left-unit-law-equiv f)

    preserves-comp-simpson-comp-equiv :
      ( X Y Z : UU-Fin l n) (e : type-UU-Fin n X ≃ type-UU-Fin n Y) →
      ( f : type-UU-Fin n Y ≃ type-UU-Fin n Z) →
      Id
        ( simpson-comp-equiv X Z (f ∘e e))
        ( ( simpson-comp-equiv Y Z f) ∘e ( simpson-comp-equiv X Y e))
    preserves-comp-simpson-comp-equiv X Y Z e f =
      eq-htpy-equiv
        ( λ h → associative-comp-equiv h e f)

  private
    lemma-sign-comp :
      (X X' : UU-Fin l n) ( e : type-UU-Fin n X ≃ type-UU-Fin n X') →
      (f f' : (Fin n ≃ type-UU-Fin n X)) →
      Id
        ( sign-homomorphism-Fin-two n X (f ∘e inv-equiv f'))
        ( sign-homomorphism-Fin-two n X'
          ( ( map-simpson-comp-equiv X X' e f) ∘e
            ( inv-equiv (map-simpson-comp-equiv X X' e f'))))
    lemma-sign-comp X X' e f f' = 
      inv
        ( preserves-conjugation-sign-homomorphism-Fin-two n X X'
          ( f ∘e inv-equiv f')
          ( e)) ∙
        ( ap
          ( sign-homomorphism-Fin-two n X')
          ( ( ap
            ( λ h → e ∘e h)
            ( ( associative-comp-equiv ( inv-equiv e) (inv-equiv f') f) ∙
              ( ap (λ h → f ∘e h) (inv (distributive-inv-comp-equiv f' e)))) ∙
            ( inv
              ( associative-comp-equiv
                ( inv-equiv (map-simpson-comp-equiv X X' e f'))
                ( f)
                ( e))))))

  preserves-sign-comp-simpson-comp-equiv :
    (X X' : UU-Fin l n) ( e : type-UU-Fin n X ≃ type-UU-Fin n X') →
    (f f' : (Fin n ≃ type-UU-Fin n X)) →
    ( sim-Eq-Rel (sign-comp-Eq-Rel n X) f f' ↔
      sim-Eq-Rel
        ( sign-comp-Eq-Rel n X')
        ( map-simpson-comp-equiv X X' e f)
        ( map-simpson-comp-equiv X X' e f'))
  pr1 (preserves-sign-comp-simpson-comp-equiv X X' e f f') P =
    P ∙ lemma-sign-comp X X' e f f'
  pr2 (preserves-sign-comp-simpson-comp-equiv X X' e f f') P =
    P ∙ inv (lemma-sign-comp X X' e f f')
```


```agda
module _
  {l : Level}
  where

    sign-comp-aut-succ-succ-Fin : (n : ℕ) →
      type-Group (symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))) →
      ( Fin (succ-ℕ (succ-ℕ n)) ≃
        raise l (Fin (succ-ℕ (succ-ℕ n))))
    sign-comp-aut-succ-succ-Fin n h =
      h ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))

module _
  {l : Level}
  where

  simpson-delooping-sign : (n : ℕ) →
    hom-Concrete-Group (UU-Fin-Group l n) (UU-Fin-Group (lsuc lzero ⊔ l) 2)
  simpson-delooping-sign =
    quotient-delooping-sign
      ( λ n X → Fin n ≃ type-UU-Fin n X)
      ( λ n X → sign-comp-Eq-Rel n X)
      ( is-decidable-sign-comp-Eq-Rel)
      ( equiv-fin-2-quotient-sign-comp-equiv-Fin)
      ( simpson-comp-equiv)
      ( preserves-id-equiv-simpson-comp-equiv)
      ( preserves-sign-comp-simpson-comp-equiv)
      ( sign-comp-aut-succ-succ-Fin)
      ( λ n →
        not-sign-comp-transposition-count
          ( (succ-ℕ (succ-ℕ n), equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))

  eq-simpson-delooping-sign-homomorphism : (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group (lsuc lzero ⊔ l) 2))
        ( comp-hom-Group
          ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group (lsuc lzero ⊔ l) 2))
          ( hom-group-hom-Concrete-Group
            ( UU-Fin-Group l (succ-ℕ (succ-ℕ n)))
            ( UU-Fin-Group (lsuc lzero ⊔ l) 2)
            ( simpson-delooping-sign (succ-ℕ (succ-ℕ n))))
          ( hom-inv-iso-Group
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
            ( iso-loop-group-fin-UU-Fin-Group l (succ-ℕ (succ-ℕ n)))))
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group (lsuc lzero ⊔ l) 2))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( symmetric-Group (Fin-Set 2))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group (lsuc lzero ⊔ l) 2))
          ( symmetric-abstract-UU-fin-group-quotient-hom
            ( λ n X → Fin n ≃ type-UU-Fin n X)
            ( λ n X → sign-comp-Eq-Rel n X)
            ( is-decidable-sign-comp-Eq-Rel)
            ( equiv-fin-2-quotient-sign-comp-equiv-Fin)
            ( simpson-comp-equiv)
            ( preserves-id-equiv-simpson-comp-equiv)
            ( preserves-sign-comp-simpson-comp-equiv)
            ( sign-comp-aut-succ-succ-Fin)
            ( λ n →
              not-sign-comp-transposition-count
                ( (succ-ℕ (succ-ℕ n), equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                ( star))
            ( n))
          ( sign-homomorphism
            ( succ-ℕ (succ-ℕ n))
            ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  eq-simpson-delooping-sign-homomorphism =
    eq-quotient-delooping-sign-homomorphism
      ( λ n X → Fin n ≃ type-UU-Fin n X)
      ( λ n X → sign-comp-Eq-Rel n X)
      ( is-decidable-sign-comp-Eq-Rel)
      ( equiv-fin-2-quotient-sign-comp-equiv-Fin)
      ( simpson-comp-equiv)
      ( preserves-id-equiv-simpson-comp-equiv)
      ( preserves-sign-comp-simpson-comp-equiv)
      ( sign-comp-aut-succ-succ-Fin)
      ( λ n →
        not-sign-comp-transposition-count
          ( (succ-ℕ (succ-ℕ n), equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( star))
```

