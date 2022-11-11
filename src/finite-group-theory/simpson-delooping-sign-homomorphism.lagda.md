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
    
  abstract
    mere-equiv-fin-2-quotient-sign-comp :
      mere-equiv (Fin 2) (quotient-sign-comp n X)
    mere-equiv-fin-2-quotient-sign-comp =
      map-trunc-Prop
        ( equiv-fin-2-quotient-sign-comp-equiv-Fin)
        ( has-cardinality-type-UU-Fin n X)

module _
  { l : Level}
  where
  
  map-simpson-delooping-sign : (n : ℕ) →
    classifying-type-Concrete-Group
      ( UU-Fin-Group l n) →
    classifying-type-Concrete-Group
      ( UU-Fin-Group (lsuc lzero ⊔ l) 2)
  map-simpson-delooping-sign zero-ℕ X = Fin-UU-Fin (lsuc lzero ⊔ l) 2
  map-simpson-delooping-sign (succ-ℕ zero-ℕ) X = Fin-UU-Fin (lsuc lzero ⊔ l) 2
  pr1 (map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)) X) =
    quotient-sign-comp (succ-ℕ (succ-ℕ n)) X 
  pr2 (map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)) X) =
    mere-equiv-fin-2-quotient-sign-comp (succ-ℕ (succ-ℕ n)) X star

  simpson-delooping-sign : (n : ℕ) →
    hom-Concrete-Group (UU-Fin-Group l n) (UU-Fin-Group (lsuc lzero ⊔ l) 2)
  pr1 (simpson-delooping-sign n) = map-simpson-delooping-sign n
  pr2 (simpson-delooping-sign zero-ℕ) = refl
  pr2 (simpson-delooping-sign (succ-ℕ zero-ℕ)) = refl
  pr2 (simpson-delooping-sign (succ-ℕ (succ-ℕ n))) =
    eq-pair-Σ
      ( eq-equiv
        ( pr1
          ( map-simpson-delooping-sign
            ( succ-ℕ (succ-ℕ n))
            ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))))
        ( raise (lsuc lzero ⊔ l) (Fin 2))
        ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
          ( inv-equiv
            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
              ( succ-ℕ (succ-ℕ n))
              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
              ( star)
              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
      ( eq-is-prop is-prop-type-trunc-Prop)
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

  private
    raise-UU-Fin-Fin : (n : ℕ) → UU-Fin l n
    pr1 (raise-UU-Fin-Fin n) = raise l (Fin n)
    pr2 (raise-UU-Fin-Fin n) = unit-trunc-Prop (equiv-raise l (Fin n))

    simpson-comp-loop-Fin : (n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))) →
      ( ( Fin (succ-ℕ (succ-ℕ n)) ≃
          ( type-UU-Fin (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))) ≃
        ( Fin (succ-ℕ (succ-ℕ n)) ≃
          ( type-UU-Fin (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))))
    simpson-comp-loop-Fin n p =
      simpson-comp-equiv
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( p))

    map-simpson-comp-loop-Fin : (n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))) →
      ( Fin (succ-ℕ (succ-ℕ n)) ≃
        ( type-UU-Fin (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))) →
      ( Fin (succ-ℕ (succ-ℕ n)) ≃
        ( type-UU-Fin (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
    map-simpson-comp-loop-Fin n p =
      map-equiv (simpson-comp-loop-Fin n p)

    quotient-sign-comp-set-Fin : (n : ℕ) → Set (lsuc lzero ⊔ l)
    quotient-sign-comp-set-Fin n =
      quotient-sign-comp-Set n (raise-UU-Fin-Fin n)

    quotient-map-sign-comp-Fin : (n : ℕ) →
      ( Fin n ≃ type-UU-Fin n (raise-UU-Fin-Fin n)) →
      ( type-Set (quotient-sign-comp-set-Fin n))
    quotient-map-sign-comp-Fin n =
      class
        ( sign-comp-Eq-Rel n (raise-UU-Fin-Fin n))

    quotient-reflecting-map-sign-comp-Fin : (n : ℕ) →
      reflecting-map-Eq-Rel
        ( sign-comp-Eq-Rel n (raise-UU-Fin-Fin n))
        ( type-Set (quotient-sign-comp-set-Fin n))
    quotient-reflecting-map-sign-comp-Fin n =
      quotient-reflecting-map-equivalence-class
        ( sign-comp-Eq-Rel n (raise-UU-Fin-Fin n))

    sign-comp-aut-succ-succ-Fin : (n : ℕ) →
      type-Group (symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))) →
      ( Fin (succ-ℕ (succ-ℕ n)) ≃
        ( type-UU-Fin (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
    sign-comp-aut-succ-succ-Fin n h =
      h ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))

  map-simpson-delooping-sign-loop : (n : ℕ) (X Y : UU l) →
    (eX : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) X) →
    (eY : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) Y) →
    Id X Y →
    Id
      ( quotient-sign-comp (succ-ℕ (succ-ℕ n)) (pair X eX))
      ( quotient-sign-comp (succ-ℕ (succ-ℕ n)) (pair Y eY))
  map-simpson-delooping-sign-loop n X Y eX eY p =
    ap (quotient-sign-comp (succ-ℕ (succ-ℕ n))) (eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))

  private
    map-simpson-delooping-sign-loop-Fin : (n : ℕ) →
      type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))) →
      type-Group (loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
    map-simpson-delooping-sign-loop-Fin n =
      map-simpson-delooping-sign-loop n
        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
        ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
        ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))

  simpson-delooping-sign-loop : (n : ℕ) →
    type-hom-Group
      ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
      ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
  pr1 (simpson-delooping-sign-loop n) = map-simpson-delooping-sign-loop-Fin n
  pr2 (simpson-delooping-sign-loop n) p q =
    ( ap
      ( ap (quotient-sign-comp (succ-ℕ (succ-ℕ n))))
      ( ( ap
        ( λ w → eq-pair-Σ (p ∙ q) w)
        ( eq-is-prop
          ( is-trunc-Id
            ( is-prop-type-trunc-Prop _ (unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))) ∙
        ( inv
          ( comp-eq-pair-Σ
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( p)
            ( q)
            ( eq-is-prop is-prop-type-trunc-Prop)
            ( eq-is-prop is-prop-type-trunc-Prop))))) ∙
      ( ap-concat
        ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))
        ( eq-pair-Σ q (eq-is-prop is-prop-type-trunc-Prop)))

  abstract
    coherence-square-map-simpson-delooping-sign-loop-Set : (n : ℕ) →
      ( X Y : UU l) ( eX : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) X) →
      ( eY : mere-equiv (Fin (succ-ℕ (succ-ℕ n))) Y) →
      ( p : Id X Y) →
      ( Id (tr (λ v → mere-equiv (Fin (succ-ℕ (succ-ℕ n))) v) p eX) eY) →
      ( sX : is-set X) ( sY : is-set Y) →
      coherence-square
        ( map-simpson-comp-equiv
          ( succ-ℕ (succ-ℕ n))
          ( pair Y eY)
          ( pair X eX)
          ( map-hom-symmetric-group-loop-group-Set
            ( pair X sX)
            ( pair Y sY)
            ( p)))
        ( class
          ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n)) (pair Y eY)))
        ( class
          ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n)) (pair X eX)))
        ( map-equiv
          ( map-hom-symmetric-group-loop-group-Set
            ( quotient-sign-comp-Set (succ-ℕ (succ-ℕ n)) (pair X eX))
            ( quotient-sign-comp-Set (succ-ℕ (succ-ℕ n)) (pair Y eY))
            ( map-simpson-delooping-sign-loop n X Y eX eY p)))
    coherence-square-map-simpson-delooping-sign-loop-Set n X .X eX .eX refl refl sX sY x =
      ( ap
        ( λ w →
          map-equiv
            ( map-hom-symmetric-group-loop-group-Set
              ( quotient-sign-comp-Set (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( quotient-sign-comp-Set (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( w))
            ( class
              ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( x)))
        ( ap
          ( λ w → ap (quotient-sign-comp (succ-ℕ (succ-ℕ n))) (eq-pair-Σ refl w))
          { x = eq-is-prop is-prop-type-trunc-Prop}
          ( eq-is-prop
            ( is-trunc-Id
              ( is-prop-type-trunc-Prop
                ( tr (mere-equiv (Fin (succ-ℕ (succ-ℕ n)))) refl eX)
                ( eX)))))) ∙
        ap
          ( class
            ( sign-comp-Eq-Rel
              ( succ-ℕ (succ-ℕ n))
              ( pair X (tr (mere-equiv (Fin (succ-ℕ (succ-ℕ n)))) refl eX))))
          ( inv
            ( htpy-eq-equiv
              ( preserves-id-equiv-simpson-comp-equiv (succ-ℕ (succ-ℕ n)) (pair X eX))
              ( x)))

  coherence-square-map-simpson-delooping-sign-loop-Fin : (n : ℕ) 
    ( p : type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))) →
    coherence-square
      ( map-simpson-comp-loop-Fin n p)
      ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
      ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
      ( map-equiv
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
          ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
          ( map-simpson-delooping-sign-loop-Fin n p)))
  coherence-square-map-simpson-delooping-sign-loop-Fin n p =
    coherence-square-map-simpson-delooping-sign-loop-Set n
      ( raise l (Fin (succ-ℕ (succ-ℕ n)))) 
      ( raise l (Fin (succ-ℕ (succ-ℕ n)))) 
      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
      ( p)
      ( eq-is-prop is-prop-type-trunc-Prop)
      ( is-set-type-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
      ( is-set-type-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))

  private
    is-contr-equiv-simpson-comp : (n : ℕ) →
      ( p : type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))) →
      is-contr
        ( Σ
          ( type-Group
            ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
          ( λ h' →
            coherence-square
              ( map-simpson-comp-loop-Fin n p)
              ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
              ( map-reflecting-map-Eq-Rel
                ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
                  ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
                (quotient-reflecting-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))))
              ( map-equiv h')))
    is-contr-equiv-simpson-comp n p =
      unique-equiv-is-set-quotient
        ( sign-comp-Eq-Rel
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
        ( quotient-reflecting-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
        ( sign-comp-Eq-Rel
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
        ( quotient-reflecting-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
        ( is-set-quotient-equivalence-class
          ( sign-comp-Eq-Rel
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
        ( is-set-quotient-equivalence-class
          ( sign-comp-Eq-Rel
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
        ( simpson-comp-loop-Fin n p)
        ( λ {x} {y} →
          preserves-sign-comp-simpson-comp-equiv
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( p))
            ( x)
            ( y))

  abstract
    eq-simpson-delooping-sign-loop-equiv-is-set-quotient : (n : ℕ) →
      ( p : type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))) →
      Id 
        ( map-hom-symmetric-group-loop-group-Set
          ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
          ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
          ( map-simpson-delooping-sign-loop-Fin n p))
        ( pr1 (center (is-contr-equiv-simpson-comp n p)))
    eq-simpson-delooping-sign-loop-equiv-is-set-quotient n p =
      ap pr1
        { x =
          pair
            ( map-hom-symmetric-group-loop-group-Set
              ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
              ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
              ( map-simpson-delooping-sign-loop-Fin n p))
            ( coherence-square-map-simpson-delooping-sign-loop-Fin n p)}
        { y = center (is-contr-equiv-simpson-comp n p)}
        ( eq-is-contr (is-contr-equiv-simpson-comp n p))

  cases-map-simpson-aut-Fin : (n : ℕ) →
    ( h : type-Group (symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))) →
    ( is-decidable
      ( sim-Eq-Rel
        ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( sign-comp-aut-succ-succ-Fin n h)
        ( map-simpson-comp-equiv (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( h)
          ( sign-comp-aut-succ-succ-Fin n h)))) →
    type-Group
      ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
  cases-map-simpson-aut-Fin n h (inl D) = id-equiv
  cases-map-simpson-aut-Fin n h (inr ND) =
    ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
      ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
      ( star)
      ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))) ∘e
      ( ( equiv-succ-Fin 2) ∘e
        ( inv-equiv
          ( equiv-fin-2-quotient-sign-comp-equiv-Fin
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))

  map-simpson-aut-Fin : (n : ℕ) →
    type-Group (symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))) → 
    type-Group
      ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
  map-simpson-aut-Fin n h =
    cases-map-simpson-aut-Fin n h
      ( is-decidable-sign-comp-Eq-Rel
        ( succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( sign-comp-aut-succ-succ-Fin n h)
        ( map-simpson-comp-equiv (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( h)
          ( sign-comp-aut-succ-succ-Fin n h)))

  eq-map-simpson-aut-fin-transposition : (n : ℕ) →
    ( Y : 2-Element-Decidable-Subtype l (raise l (Fin (succ-ℕ (succ-ℕ n))))) →
    Id
      ( map-simpson-aut-Fin n (transposition Y))
      ( ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( star)
        ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))) ∘e
        ( ( equiv-succ-Fin 2) ∘e
          ( inv-equiv
            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
              ( succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( star)
              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
  eq-map-simpson-aut-fin-transposition n Y =
    ap
      ( cases-map-simpson-aut-Fin n (transposition Y))
      { x =
        is-decidable-sign-comp-Eq-Rel
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( sign-comp-aut-succ-succ-Fin n (transposition Y))
          ( map-simpson-comp-equiv (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( transposition Y)
            ( sign-comp-aut-succ-succ-Fin n (transposition Y)))}
      { y =
        inr
          ( not-sign-comp-transposition-count
            ( pair (succ-ℕ (succ-ℕ n)) (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
            ( star)
            ( Y))}
      ( eq-is-prop
        ( is-prop-is-decidable
          ( is-prop-sim-Eq-Rel
            ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( sign-comp-aut-succ-succ-Fin n (transposition Y))
            ( map-simpson-comp-equiv (succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
              ( transposition Y)
              ( sign-comp-aut-succ-succ-Fin n (transposition Y))))))

  cases-eq-map-simpson-aut-Fin : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))) →
    ( D : is-decidable
      ( sim-Eq-Rel
        ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
        ( sign-comp-aut-succ-succ-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( p)))
        ( map-simpson-comp-loop-Fin n p
          ( sign-comp-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( p)))))) →
    ( k k' : Fin 2) →
    Id
      ( map-inv-equiv
        ( equiv-fin-2-quotient-sign-comp-equiv-Fin
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
        ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
          ( sign-comp-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( p)))))
      ( k) →
    Id
      ( map-inv-equiv
        ( equiv-fin-2-quotient-sign-comp-equiv-Fin
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
        ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
          ( map-simpson-comp-loop-Fin n p
            ( sign-comp-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                ( p))))))
      ( k') →
    Id
      ( map-equiv
        ( cases-map-simpson-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( p))
          ( D))
        ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
          ( sign-comp-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( p)))))
      ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
        ( map-simpson-comp-loop-Fin n p
          ( sign-comp-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( p)))))
  cases-eq-map-simpson-aut-Fin n p (inl D) k k' q r =
    reflects-map-reflecting-map-Eq-Rel
      ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
      ( quotient-reflecting-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
      ( D)
  cases-eq-map-simpson-aut-Fin n p (inr ND) (inl (inr star)) (inl (inr star)) q r =
    ex-falso
      ( ND
        ( map-equiv
          ( is-effective-is-set-quotient
            ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
            ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
            ( reflects-map-reflecting-map-Eq-Rel
              ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
              ( quotient-reflecting-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))))
            ( is-set-quotient-equivalence-class
              ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
            ( sign-comp-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                ( p)))
            ( map-simpson-comp-loop-Fin n p
              ( sign-comp-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                  ( p)))))
          ( is-injective-map-equiv
            ( inv-equiv
              ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
            ( q ∙ inv r))))
  cases-eq-map-simpson-aut-Fin n p (inr ND) (inl (inr star)) (inr star) q r =
    ( ap
      ( map-equiv
        ( equiv-fin-2-quotient-sign-comp-equiv-Fin
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
      ( ( ap
        ( map-equiv (equiv-succ-Fin 2))
        ( q)) ∙
        ( inv r))) ∙
       ap
        ( λ e →
          map-equiv e
            ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
              ( map-simpson-comp-loop-Fin n p
                ( sign-comp-aut-succ-succ-Fin n
                  ( map-hom-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                    ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                    ( p))))))
        ( right-inverse-law-equiv
          ( equiv-fin-2-quotient-sign-comp-equiv-Fin
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  cases-eq-map-simpson-aut-Fin n p (inr ND) (inr star) (inl (inr star)) q r =
    ( ap
      ( map-equiv
        ( equiv-fin-2-quotient-sign-comp-equiv-Fin
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
      ( ( ap
        ( map-equiv (equiv-succ-Fin 2))
        ( q)) ∙
        ( inv r))) ∙
       ap
        ( λ e →
          map-equiv e
            ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
              ( map-simpson-comp-loop-Fin n p
                ( sign-comp-aut-succ-succ-Fin n
                  ( map-hom-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                    ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                    ( p))))))
        ( right-inverse-law-equiv
          ( equiv-fin-2-quotient-sign-comp-equiv-Fin
            ( succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  cases-eq-map-simpson-aut-Fin n p (inr ND) (inr star) (inr star) q r =
    ex-falso
      ( ND
        ( map-equiv
          ( is-effective-is-set-quotient
            ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
              ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
            ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
            ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
            ( reflects-map-reflecting-map-Eq-Rel
              ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
              ( quotient-reflecting-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))))
            ( is-set-quotient-equivalence-class
              ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
            ( sign-comp-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                ( p)))
            ( map-simpson-comp-loop-Fin n p
              ( sign-comp-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                  ( p)))))
          ( is-injective-map-equiv
            ( inv-equiv
              ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
            ( q ∙ inv r))))

  eq-map-simpson-aut-Fin : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))) →
    Id
      ( map-equiv
        ( map-simpson-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( p)))
        ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
          ( sign-comp-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l(succ-ℕ (succ-ℕ n)))
              ( p)))))
      ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
        ( map-simpson-comp-loop-Fin n p
          ( sign-comp-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
              ( p)))))
  eq-map-simpson-aut-Fin n p =
     cases-eq-map-simpson-aut-Fin n p
      ( is-decidable-sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
        ( sign-comp-aut-succ-succ-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( p)))
        ( map-simpson-comp-loop-Fin n p
          ( sign-comp-aut-succ-succ-Fin n
            ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( p)))))
        ( map-inv-equiv
          ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
            ( sign-comp-aut-succ-succ-Fin n
              ( map-hom-symmetric-group-loop-group-Set
                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                ( p)))))
        ( map-inv-equiv
          ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
            ( star)
            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
          ( quotient-map-sign-comp-Fin (succ-ℕ (succ-ℕ n))
            ( map-simpson-comp-loop-Fin n p
              ( sign-comp-aut-succ-succ-Fin n
                ( map-hom-symmetric-group-loop-group-Set
                  ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                  ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                  ( p))))))
        ( refl)
        ( refl)

  eq-map-simpson-aut-loop-equiv-is-set-quotient : (n : ℕ) →
    ( p : type-Group (loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))) →
    Id 
      ( map-simpson-aut-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( p)))
      ( pr1 (center (is-contr-equiv-simpson-comp n p)))
  eq-map-simpson-aut-loop-equiv-is-set-quotient n p =
    eq-equiv-eq-one-value-equiv-is-set-quotient
      ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n))))
      ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
      ( quotient-reflecting-map-sign-comp-Fin (succ-ℕ (succ-ℕ n)))
      ( is-set-quotient-equivalence-class
        ( sign-comp-Eq-Rel (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))))
      ( inv-equiv
        ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( star)
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
      ( map-simpson-comp-loop-Fin n p)
      ( λ {x} {y} →
        preserves-sign-comp-simpson-comp-equiv
          ( succ-ℕ (succ-ℕ n))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( p))
          ( x)
          ( y))
      ( map-equiv
        ( map-simpson-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( p))))
      ( sign-comp-aut-succ-succ-Fin n
        ( map-hom-symmetric-group-loop-group-Set
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( p)))
      ( eq-map-simpson-aut-Fin n p)
      ( is-equiv-map-equiv (simpson-comp-loop-Fin n p))
      ( is-equiv-map-equiv
        ( map-simpson-aut-Fin n
          ( map-hom-symmetric-group-loop-group-Set
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
            ( p))))

  eq-simpson-delooping-sign-loop-sign-homomorphism : {l' : Level} (n : ℕ) →
    Id
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
        ( simpson-delooping-sign-loop n)
        ( hom-inv-symmetric-group-loop-group-Set
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
      ( comp-hom-Group
        ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
        ( comp-hom-Group
          ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
          ( symmetric-Group (Fin-Set 2))
          ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
          ( comp-hom-Group
            ( symmetric-Group (Fin-Set 2))
            ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
            ( hom-inv-symmetric-group-loop-group-Set
              ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
            ( hom-symmetric-group-equiv-Set
              ( Fin-Set 2)
              ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
              ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
                ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                ( star)
                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
          ( sign-homomorphism (succ-ℕ (succ-ℕ n))
            ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
        ( hom-inv-symmetric-group-equiv-Set
          ( Fin-Set (succ-ℕ (succ-ℕ n)))
          ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
  eq-simpson-delooping-sign-loop-sign-homomorphism n =
    map-inv-equiv
      ( equiv-ap-emb
        ( restriction-generating-subset-Group
          ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
          ( is-transposition-permutation-Prop {l2 = l})
          ( tr
            ( λ s →
              is-generating-subset-Group
                ( symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s))
                ( is-transposition-permutation-Prop))
            ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
            ( is-generated-transposition-symmetric-Fin-Level
              ( succ-ℕ (succ-ℕ n))
              ( pair
                ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
          ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))))
      ( eq-htpy
        ( λ (pair f s) →
          apply-universal-property-trunc-Prop s
            ( Id-Prop
              ( set-Group (loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
              ( map-emb
                ( restriction-generating-subset-Group
                  ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                  ( is-transposition-permutation-Prop)
                  ( tr
                    ( λ s₁ →
                      is-generating-subset-Group
                        (symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                        ( is-transposition-permutation-Prop))
                    ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
                    ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                      ( pair
                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                        ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                  ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
                ( comp-hom-Group
                  ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( simpson-delooping-sign-loop n)
                  ( hom-inv-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
                ( pair f s))
              ( map-emb
                ( restriction-generating-subset-Group
                  ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                  ( is-transposition-permutation-Prop)
                  ( tr
                    ( λ s₁ →
                      is-generating-subset-Group
                        ( symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                        ( is-transposition-permutation-Prop))
                    ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
                    ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                      ( pair
                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                        ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                    ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( comp-hom-Group
                    ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                    ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                    ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( comp-hom-Group
                      ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                      ( symmetric-Group (Fin-Set 2))
                      ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( comp-hom-Group
                        ( symmetric-Group (Fin-Set 2))
                        ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( hom-inv-symmetric-group-loop-group-Set
                          ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                        ( hom-symmetric-group-equiv-Set (Fin-Set 2)
                          ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
                          ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
                            ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                            ( star)
                            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
                      ( sign-homomorphism (succ-ℕ (succ-ℕ n))
                        ( pair
                          ( Fin (succ-ℕ (succ-ℕ n)))
                          ( unit-trunc-Prop id-equiv))))
                    ( hom-inv-symmetric-group-equiv-Set
                      ( Fin-Set (succ-ℕ (succ-ℕ n)))
                      ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                      ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
                ( pair f s)))
             λ (pair Y q) →
              ( eq-map-restriction-generating-subset-Group
                ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                ( is-transposition-permutation-Prop)
                ( tr
                  ( λ s₁ →
                     is-generating-subset-Group
                      ( symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                      ( is-transposition-permutation-Prop))
                  ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
                  ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                    ( pair
                      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                      ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                ( comp-hom-Group
                  ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( simpson-delooping-sign-loop n)
                  ( hom-inv-symmetric-group-loop-group-Set
                    ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
                ( pair f s)) ∙
                ( ( htpy-eq-hom-Group
                  ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                  ( id-hom-Group (loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( comp-hom-Group
                    ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( hom-inv-symmetric-group-loop-group-Set
                      ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                    ( hom-symmetric-group-loop-group-Set
                      ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( inv
                    ( is-retr-hom-inv-symmetric-group-loop-group-Set
                      ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
                  ( ap (quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                    ( eq-pair-Σ
                     ( inv
                      ( eq-equiv
                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                        ( f)))
                     ( eq-is-prop is-prop-type-trunc-Prop)))) ∙
                  ( ( ap
                    ( map-hom-Group
                      ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                      ( hom-inv-symmetric-group-loop-group-Set
                        ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
                    ( eq-simpson-delooping-sign-loop-equiv-is-set-quotient n
                      ( inv
                        ( eq-equiv
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( f))) ∙
                      ( inv
                        ( eq-map-simpson-aut-loop-equiv-is-set-quotient n
                          ( inv
                            ( eq-equiv
                              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                              ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                              ( f))))))) ∙
                    ( ( ap
                      ( λ g →
                        map-hom-Group
                          ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( hom-inv-symmetric-group-loop-group-Set
                            ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( map-simpson-aut-Fin n g))
                      ( ( commutative-inv-map-hom-symmetric-group-loop-group-Set
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                          ( eq-equiv
                            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                            ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                            ( f))
                          ( pr2 (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                          ( pr2 (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))) ∙
                          ( ap inv-equiv
                            ( ( ap
                              ( map-hom-symmetric-group-loop-group-Set
                                  ( raise l (Fin (succ-ℕ (succ-ℕ n))) ,
                                    pr2 (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                                  ( raise l (Fin (succ-ℕ (succ-ℕ n))) ,
                                    pr2 (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
                              ( ( ap
                                ( eq-equiv
                                  ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                  ( raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                ( inv (inv-inv-equiv f))) ∙
                                ( inv
                                  ( commutativity-inv-eq-equiv
                                    ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                    ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                    ( inv-equiv f))))) ∙
                              ( ( htpy-eq-hom-Group
                                ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                                ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                                ( comp-hom-Group
                                  ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                                  ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                                  ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                                  ( hom-symmetric-group-loop-group-Set
                                    ( raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                                  ( hom-inv-symmetric-group-loop-group-Set
                                    ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
                                ( id-hom-Group
                                  ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
                                ( is-sec-hom-inv-symmetric-group-loop-group-Set
                                  ( raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                                ( inv-equiv f)) ∙
                                ( ( ap inv-equiv (inv q)) ∙
                                  ( own-inverse-is-involution
                                    ( is-involution-map-transposition Y)))))))) ∙
                      ( ( ap
                        ( map-hom-Group
                          ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                          ( hom-inv-symmetric-group-loop-group-Set
                            ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))))
                        ( ( ap
                          ( map-simpson-aut-Fin n)
                          ( own-inverse-is-involution
                            ( is-involution-map-transposition Y))) ∙
                          ( ( eq-map-simpson-aut-fin-transposition n Y) ∙
                            ( ap
                              ( λ e →
                                ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
                                  ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                  ( star)
                                  ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))) ∘e
                                  ( e ∘e
                                    ( inv-equiv
                                      ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
                                        ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                        ( star)
                                        ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                              ( ( inv
                                ( eq-sign-homomorphism-transposition (succ-ℕ (succ-ℕ n))
                                  ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))
                                  ( map-equiv
                                    ( equiv-universes-2-Element-Decidable-Subtype
                                      ( Fin (succ-ℕ (succ-ℕ n)))
                                      ( l)
                                      ( lzero))
                                    ( transposition-conjugation-equiv {l4 = l}
                                      ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                      ( Fin (succ-ℕ (succ-ℕ n)))
                                      ( inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                      ( Y))))) ∙
                                ( ap
                                  ( map-hom-Group
                                    ( symmetric-Group
                                      ( set-UU-Fin (succ-ℕ (succ-ℕ n))
                                       ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
                                    ( symmetric-Group (Fin-Set 2))
                                    ( sign-homomorphism
                                      ( succ-ℕ (succ-ℕ n))
                                      ( pair (Fin (succ-ℕ (succ-ℕ n))) (unit-trunc-Prop id-equiv))))
                                  ( ( inv
                                    ( eq-equiv-universes-transposition (Fin (succ-ℕ (succ-ℕ n)))
                                      ( l)
                                      ( lzero)
                                      ( transposition-conjugation-equiv
                                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                        ( Fin (succ-ℕ (succ-ℕ n)))
                                        ( inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                        ( Y)))) ∙
                                    ( ( eq-htpy-equiv
                                      ( correct-transposition-conjugation-equiv
                                        ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                        ( Fin (succ-ℕ (succ-ℕ n)))
                                        ( inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                        ( Y))) ∙
                                      ( ( associative-comp-equiv
                                        ( inv-equiv (inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
                                        ( transposition Y)
                                        ( inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))) ∙
                                        ( ( ap
                                          ( λ e →
                                            inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) ∘e
                                              ( transposition Y ∘e e))
                                          ( inv-inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))) ∙
                                          ( ap
                                            ( λ e →
                                              inv-equiv (equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))) ∘e
                                                ( e ∘e equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))
                                            ( q)))))))))))) ∙
                        ( inv
                          ( eq-map-restriction-generating-subset-Group
                            ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                            ( is-transposition-permutation-Prop)
                            ( tr
                              ( λ s₁ →
                                 is-generating-subset-Group
                                  ( symmetric-Group (pair (raise l (Fin (succ-ℕ (succ-ℕ n)))) s₁))
                                  ( is-transposition-permutation-Prop))
                              ( eq-is-prop (is-prop-is-set (raise l (Fin (succ-ℕ (succ-ℕ n))))))
                              ( is-generated-transposition-symmetric-Fin-Level (succ-ℕ (succ-ℕ n))
                                ( pair
                                  ( raise l (Fin (succ-ℕ (succ-ℕ n))))
                                  ( unit-trunc-Prop (equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                            ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                            ( comp-hom-Group
                              ( symmetric-Group (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                              ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                              ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                              ( comp-hom-Group
                                ( symmetric-Group (Fin-Set (succ-ℕ (succ-ℕ n))))
                                ( symmetric-Group (Fin-Set 2))
                                ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                                ( comp-hom-Group
                                  ( symmetric-Group (Fin-Set 2))
                                  ( symmetric-Group (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( hom-inv-symmetric-group-loop-group-Set
                                    ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
                                  ( hom-symmetric-group-equiv-Set
                                    ( Fin-Set 2)
                                    ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
                                    ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
                                      ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                                      ( star)
                                      ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
                                ( sign-homomorphism (succ-ℕ (succ-ℕ n))
                                  ( pair
                                    ( Fin (succ-ℕ (succ-ℕ n)))
                                    ( unit-trunc-Prop id-equiv))))
                              ( hom-inv-symmetric-group-equiv-Set
                                ( Fin-Set (succ-ℕ (succ-ℕ n)))
                                ( raise-Fin-Set l (succ-ℕ (succ-ℕ n)))
                                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))
                            ( pair f s)))))))))

  eq-simpson-delooping-loop-UU-Fin-Group : (n : ℕ) →
    Id
      ( comp-hom-Group
        ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
        ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
        ( abstract-group-Concrete-Group
          ( UU-Fin-Group (lsuc lzero ⊔ l) 2))
        ( hom-iso-Group
          ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group (lsuc lzero ⊔ l) 2))
          ( comp-iso-Group
            ( loop-group-Set (quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (raise-Set (lsuc lzero ⊔ l) (Fin-Set 2)))
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group (lsuc lzero ⊔ l) 2))
            ( inv-iso-Group
              ( abstract-group-Concrete-Group (UU-Fin-Group (lsuc lzero ⊔ l) 2))
              ( loop-group-Set (raise-Set (lsuc lzero ⊔ l) (Fin-Set 2)))
              ( iso-loop-group-fin-UU-Fin-Group (lsuc lzero ⊔ l) 2))
            ( iso-loop-group-equiv-Set
              ( quotient-sign-comp-set-Fin (succ-ℕ (succ-ℕ n)))
              ( raise-Set (lsuc lzero ⊔ l) (Fin-Set 2))
              ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                ( inv-equiv
                  ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                    ( succ-ℕ (succ-ℕ n))
                    ( raise-UU-Fin-Fin (succ-ℕ (succ-ℕ n)))
                    ( star)
                    ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))))
        ( simpson-delooping-sign-loop n))
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
        ( hom-iso-Group
          ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
          ( abstract-group-Concrete-Group
            ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
          ( inv-iso-Group
            ( abstract-group-Concrete-Group
              ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
            ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
            ( iso-loop-group-fin-UU-Fin-Group l (succ-ℕ (succ-ℕ n))))))
  eq-simpson-delooping-loop-UU-Fin-Group n =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap
            ( λ r → eq-pair-Σ r (eq-is-prop is-prop-type-trunc-Prop))
            ( ap inv
              ( inv
                ( comp-eq-equiv
                  ( raise (lsuc lzero ⊔ l) (Fin 2))
                  ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                    ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                  ( raise (lsuc lzero ⊔ l) (Fin 2))
                  ( ( equiv-eq
                    ( inv
                      ( ap
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))) ∘e
                    ( inv-equiv
                      ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                        ( inv-equiv
                          ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                            ( succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                            ( star)
                            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))
                  ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                    ( inv-equiv
                      ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                        ( succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                        ( star)
                        ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))) ∙
                ( ap
                  ( λ r →
                    ( r) ∙
                      ( eq-equiv
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                        ( raise (lsuc lzero ⊔ l) (Fin 2))
                        ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                          ( inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))
                  (  inv
                    ( comp-eq-equiv
                      ( raise (lsuc lzero ⊔ l) (Fin 2))
                      ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                      ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                      ( inv-equiv
                        ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                          ( inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                      ( equiv-eq
                        ( inv
                          ( ap
                            ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                            ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))))) ∙
                    ( ( ap
                      ( λ r → r ∙
                        eq-equiv
                          ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                          ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                          ( equiv-eq
                            ( inv
                              ( ap
                                ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                                ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))))
                      ( inv
                        ( commutativity-inv-eq-equiv
                          ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                          ( raise (lsuc lzero ⊔ l) (Fin 2))
                          ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                            ( inv-equiv
                              ( equiv-fin-2-quotient-sign-comp-equiv-Fin (succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                ( star)
                                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))) ∙
                      ( ap
                        ( λ e →
                          inv
                            ( eq-equiv
                              ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                              ( raise (lsuc lzero ⊔ l) (Fin 2))
                              ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                                ( inv-equiv
                                  ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                                    ( succ-ℕ (succ-ℕ n))
                                    ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                    ( star)
                                    ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))) ∙
                            ( map-equiv e
                              ( inv
                                ( ap
                                  ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                                  ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))))
                        ( left-inverse-law-equiv equiv-univalence)))))) ∙
              ( ( distributive-inv-concat
                ( ( inv
                  ( eq-equiv
                    ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                      ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                    ( raise (lsuc lzero ⊔ l) (Fin 2))
                    ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                      ( inv-equiv
                        ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                          ( star)
                          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))) ∙
                  ( inv
                    ( ap
                      ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))))
                ( eq-equiv
                  ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                    ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                  ( raise (lsuc lzero ⊔ l) (Fin 2))
                  ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                    ( inv-equiv (equiv-fin-2-quotient-sign-comp-equiv-Fin
                      ( succ-ℕ (succ-ℕ n))
                      ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                      ( star)
                      ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))) ∙
                ( ap
                  ( λ r →
                    inv
                      ( eq-equiv
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                        ( raise (lsuc lzero ⊔ l) (Fin 2))
                        ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                          ( inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))) ∙
                      ( r))
                  ( ( distributive-inv-concat
                    ( inv
                      ( eq-equiv
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                        ( raise (lsuc lzero ⊔ l) (Fin 2))
                        ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                          ( inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))
                    ( inv
                      ( ap
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                        ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))) ∙
                    ( ap
                      ( λ r →
                        ( r) ∙
                          ( inv
                            ( inv
                              ( eq-equiv
                                ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                                  ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                                ( raise (lsuc lzero ⊔ l) (type-Set (Fin-Set 2)))
                                ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                                  ( inv-equiv
                                    ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                                      ( succ-ℕ (succ-ℕ n))
                                      ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                      ( star)
                                      ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))))
                      ( inv-inv
                        ( ap
                          ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                          ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))) ∙
                      ( ap
                        ( λ r →
                          ( ap
                            ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                            ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                            ( r))
                        ( inv-inv
                          ( eq-equiv
                            ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                            ( raise (lsuc lzero ⊔ l) (Fin 2))
                            ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                              ( inv-equiv
                                ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                                  ( succ-ℕ (succ-ℕ n))
                                  ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                  ( star)
                                  ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))))))))))) ∙
            ( ( ( ap
              ( eq-pair-Σ
                ( ( inv
                  ( eq-equiv
                    ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                      ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                    ( raise (lsuc lzero ⊔ l) (Fin 2))
                    ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                      ( inv-equiv
                        ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                          ( star)
                          ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))) ∙
                  ( ( ap
                    ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                    ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                    ( eq-equiv
                      ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                      ( raise (lsuc lzero ⊔ l) (Fin 2))
                      ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                        ( inv-equiv
                          ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                            ( succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                            ( star)
                            ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))))
                ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
                ( ( inv
                  ( comp-eq-pair-Σ
                    ( pr2 (Fin-UU-Fin (lsuc lzero ⊔ l) 2))
                    ( mere-equiv-fin-2-quotient-sign-comp
                      ( succ-ℕ (succ-ℕ n))
                      ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                      ( star))
                    ( pr2 (Fin-UU-Fin (lsuc lzero ⊔ l) 2))
                    ( inv
                      ( eq-equiv
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                        ( raise (lsuc lzero ⊔ l) (Fin 2))
                        ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                          ( inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))
                    ( ( ap
                      ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                      ( eq-equiv
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                        ( raise (lsuc lzero ⊔ l) (Fin 2))
                        ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                          ( inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))
                    ( eq-is-prop is-prop-type-trunc-Prop)
                    ( _))) ∙
                  ( ap
                    ( λ r →
                      ( eq-pair-Σ
                        ( inv
                          ( eq-equiv
                            ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                            ( raise (lsuc lzero ⊔ l) (Fin 2))
                            ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                              ( inv-equiv
                                ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                                  ( succ-ℕ (succ-ℕ n))
                                  ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                  ( star)
                                  ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))
                        ( eq-is-prop is-prop-type-trunc-Prop)) ∙
                        ( r))
                    ( ( inv
                      ( comp-eq-pair-Σ
                        ( mere-equiv-fin-2-quotient-sign-comp
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                          ( star))
                        ( mere-equiv-fin-2-quotient-sign-comp
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                          ( star))
                        ( pr2 (Fin-UU-Fin (lsuc lzero ⊔ l) 2))
                        ( ap
                          ( quotient-sign-comp (succ-ℕ (succ-ℕ n)))
                          ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))
                        ( eq-equiv
                          ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                          ( raise (lsuc lzero ⊔ l) (Fin 2))
                          ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                            ( inv-equiv
                              ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                                ( succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                ( star)
                                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                        ( eq-is-prop is-prop-type-trunc-Prop)
                        ( eq-is-prop is-prop-type-trunc-Prop))) ∙
                      ( ap
                        ( λ r →
                          ( r) ∙
                            ( eq-pair-Σ
                              ( eq-equiv
                                ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                                  ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                                ( raise (lsuc lzero ⊔ l) (Fin 2))
                                ( ( equiv-raise (lsuc lzero ⊔ l) (Fin 2)) ∘e
                                  ( inv-equiv
                                    ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                                      ( succ-ℕ (succ-ℕ n))
                                      ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                      ( star)
                                      ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n))))))))
                              ( eq-is-prop is-prop-type-trunc-Prop)))
                        ( ( ap
                          ( λ w → eq-pair-Σ (pr1 w) (pr2 w))
                          { y =
                            pair-eq-Σ
                              ( ap
                                ( map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)))
                                ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))}
                          ( eq-pair-Σ
                            ( inv
                              ( ap-pair-eq-Σ
                                ( UU-Fin l (succ-ℕ (succ-ℕ n)))
                                ( map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)))
                                ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))
                            ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _))))) ∙
                           issec-pair-eq-Σ
                            ( map-simpson-delooping-sign (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                            ( map-simpson-delooping-sign (succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                            ( ap
                              ( map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)))
                              ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))))))))) ∙
              ( ( ap
                ( λ r →
                  ( r) ∙
                    ( ( ap
                      ( map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop))) ∙
                      ( eq-pair-Σ
                        ( eq-equiv
                          ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                            ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                          ( raise (lsuc lzero ⊔ l) (Fin 2))
                          ( equiv-raise (lsuc lzero ⊔ l) (Fin 2) ∘e
                            inv-equiv
                              ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                                ( succ-ℕ (succ-ℕ n))
                                ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                                ( star)
                                ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
                        ( eq-is-prop is-prop-type-trunc-Prop))))
                ( ( ap
                  ( eq-pair-Σ
                    ( inv
                      ( eq-equiv
                        ( quotient-sign-comp
                          ( succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                        ( raise (lsuc lzero ⊔ l) (Fin 2))
                        ( equiv-raise (lsuc lzero ⊔ l) (Fin 2) ∘e
                          inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))))
                  ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
                  ( inv
                    ( inv-eq-pair-Σ
                      ( mere-equiv-fin-2-quotient-sign-comp
                        ( succ-ℕ (succ-ℕ n))
                        ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                        ( star))
                      ( pr2 (Fin-UU-Fin (lsuc lzero ⊔ l) 2))
                      ( eq-equiv
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                        ( raise (lsuc lzero ⊔ l) (Fin 2))
                        ( equiv-raise (lsuc lzero ⊔ l) (Fin 2) ∘e
                          inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
                      ( eq-is-prop is-prop-type-trunc-Prop))))) ∙
                ( inv
                  ( eq-tr-type-Ω
                    ( eq-pair-Σ
                      ( eq-equiv
                        ( quotient-sign-comp (succ-ℕ (succ-ℕ n))
                          ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n))))
                        ( raise (lsuc lzero ⊔ l) (Fin 2))
                        ( equiv-raise (lsuc lzero ⊔ l) (Fin 2) ∘e
                          inv-equiv
                            ( equiv-fin-2-quotient-sign-comp-equiv-Fin
                              ( succ-ℕ (succ-ℕ n))
                              ( Fin-UU-Fin l (succ-ℕ (succ-ℕ n)))
                              ( star)
                              ( equiv-raise l (Fin (succ-ℕ (succ-ℕ n)))))))
                      (eq-is-prop is-prop-type-trunc-Prop))
                    ( ap (map-simpson-delooping-sign (succ-ℕ (succ-ℕ n)))
                      ( eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)))))))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group
            ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n)))))
          ( semigroup-Group
            ( abstract-group-Concrete-Group (UU-Fin-Group (lsuc lzero ⊔ l) 2)))
          ( pr1
            ( comp-hom-Group
              ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
              ( abstract-group-Concrete-Group
                ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
              ( abstract-group-Concrete-Group (UU-Fin-Group (lsuc lzero ⊔ l) 2))
              ( hom-group-hom-Concrete-Group
                ( UU-Fin-Group l (succ-ℕ (succ-ℕ n)))
                ( UU-Fin-Group (lsuc lzero ⊔ l) 2)
                ( simpson-delooping-sign (succ-ℕ (succ-ℕ n))))
              ( hom-iso-Group
                ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                ( abstract-group-Concrete-Group
                  ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
                ( inv-iso-Group
                  ( abstract-group-Concrete-Group
                    ( UU-Fin-Group l (succ-ℕ (succ-ℕ n))))
                  ( loop-group-Set (raise-Fin-Set l (succ-ℕ (succ-ℕ n))))
                  ( iso-loop-group-fin-UU-Fin-Group l (succ-ℕ (succ-ℕ n)))))))))
```

