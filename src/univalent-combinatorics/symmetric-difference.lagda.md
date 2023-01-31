# Symmetric difference of finite subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.symmetric-difference where

open import foundation.symmetric-difference public

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers using
  (mul-ℕ; left-unit-law-mul-ℕ)
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-subtypes using
  ( decidable-subtype; type-decidable-subtype)
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.intersections-subtypes using
  ( intersection-decidable-subtype)
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels
open import foundation.xor

open import univalent-combinatorics.coproduct-types using
  ( coprod-eq-is-finite; is-finite-coprod)
open import univalent-combinatorics.decidable-subtypes using
  ( is-finite-type-decidable-subtype)
open import univalent-combinatorics.finite-types using
  ( UU-Fin; type-UU-Fin; has-cardinality-type-UU-Fin;
    number-of-elements-is-finite; is-finite; is-finite-has-cardinality;
    number-of-elements-has-finite-cardinality;
    all-elements-equal-has-finite-cardinality; has-finite-cardinality-is-finite;
    mere-equiv-has-finite-cardinality)
```

```agda
module _
  {l l1 l2 : Level} (X : UU l) (F : is-finite X)
  (P : decidable-subtype l1 X)
  (Q : decidable-subtype l2 X)
  
  where

  eq-symmetric-difference :
    Id
      ( add-ℕ
        ( number-of-elements-is-finite
          ( is-finite-type-decidable-subtype P F))        
        ( number-of-elements-is-finite (is-finite-type-decidable-subtype Q F)))
      ( add-ℕ
        ( number-of-elements-is-finite
          ( is-finite-type-decidable-subtype
            ( symmetric-difference-decidable-subtype P Q) F))
        ( mul-ℕ
          2
          ( number-of-elements-is-finite
            ( is-finite-type-decidable-subtype
              ( intersection-decidable-subtype P Q)
              ( F)))))
  eq-symmetric-difference =
    ( ( coprod-eq-is-finite
      ( is-finite-type-decidable-subtype P F)
      ( is-finite-type-decidable-subtype Q F))) ∙
      ( ( ap
        ( number-of-elements-has-finite-cardinality)
        ( all-elements-equal-has-finite-cardinality
          ( has-finite-cardinality-is-finite
            ( is-finite-coprod
              ( is-finite-type-decidable-subtype P F)
              ( is-finite-type-decidable-subtype Q F)))
          ( pair
            ( number-of-elements-is-finite
              ( is-finite-coprod-symmetric-difference))
            ( transitive-mere-equiv
              ( mere-equiv-has-finite-cardinality
                ( has-finite-cardinality-is-finite
                  ( is-finite-coprod-symmetric-difference)))
              ( unit-trunc-Prop
                ( inv-equiv (equiv-symmetric-difference P Q))))))) ∙
        ( inv
          ( coprod-eq-is-finite
            ( is-finite-type-decidable-subtype
              ( symmetric-difference-decidable-subtype P Q) F)
            ( is-finite-coprod is-finite-intersection is-finite-intersection)) ∙
          ( ap
            ( λ n →
              add-ℕ
                ( number-of-elements-decidable-subtype-X
                  ( symmetric-difference-decidable-subtype P Q))
                ( n))
            ( ( inv
              ( coprod-eq-is-finite
                ( is-finite-intersection)
                ( is-finite-intersection))) ∙
              ( ap
                ( λ n →
                  add-ℕ
                    ( n)
                    ( number-of-elements-decidable-subtype-X
                      ( intersection-decidable-subtype P Q)))
                ( inv
                  ( left-unit-law-mul-ℕ
                    ( number-of-elements-decidable-subtype-X
                      ( intersection-decidable-subtype P Q)))))))))
    where
    is-finite-intersection :
      is-finite (type-decidable-subtype (intersection-decidable-subtype P Q))
    is-finite-intersection =
      is-finite-type-decidable-subtype (intersection-decidable-subtype P Q) F
    number-of-elements-decidable-subtype-X : {l' : Level} →
      (decidable-subtype l' X) → ℕ
    number-of-elements-decidable-subtype-X R =
      number-of-elements-is-finite (is-finite-type-decidable-subtype R F)
    is-finite-coprod-symmetric-difference :
      is-finite
        ( ( type-decidable-subtype
            ( symmetric-difference-decidable-subtype P Q)) +
          ( ( type-decidable-subtype
              ( intersection-decidable-subtype P Q)) +
            ( type-decidable-subtype
              ( intersection-decidable-subtype P Q))))
    is-finite-coprod-symmetric-difference =
      is-finite-coprod
        ( is-finite-type-decidable-subtype
          ( symmetric-difference-decidable-subtype P Q)
          ( F))
        ( is-finite-coprod is-finite-intersection is-finite-intersection)
