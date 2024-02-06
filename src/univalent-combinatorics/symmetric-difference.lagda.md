# Symmetric difference of finite subtypes

```agda
module univalent-combinatorics.symmetric-difference where

open import foundation.symmetric-difference public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
```

</details>

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
        ( 2 *ℕ
          ( number-of-elements-is-finite
            ( is-finite-type-decidable-subtype
              ( intersection-decidable-subtype P Q)
              ( F)))))
  eq-symmetric-difference =
    ( ( coproduct-eq-is-finite
        ( is-finite-type-decidable-subtype P F)
        ( is-finite-type-decidable-subtype Q F))) ∙
      ( ( ap
          ( number-of-elements-has-finite-cardinality)
          ( all-elements-equal-has-finite-cardinality
            ( has-finite-cardinality-is-finite
              ( is-finite-coproduct
                ( is-finite-type-decidable-subtype P F)
                ( is-finite-type-decidable-subtype Q F)))
            ( pair
              ( number-of-elements-is-finite
                ( is-finite-coproduct-symmetric-difference))
              ( transitive-mere-equiv _ _ _
                ( unit-trunc-Prop
                  ( inv-equiv (equiv-symmetric-difference P Q)))
                ( mere-equiv-has-finite-cardinality
                  ( has-finite-cardinality-is-finite
                    ( is-finite-coproduct-symmetric-difference))))))) ∙
        ( inv
          ( coproduct-eq-is-finite
            ( is-finite-type-decidable-subtype
              ( symmetric-difference-decidable-subtype P Q) F)
            ( is-finite-coproduct
              ( is-finite-intersection)
              ( is-finite-intersection))) ∙
          ( ap
            ( ( number-of-elements-decidable-subtype-X
                ( symmetric-difference-decidable-subtype P Q)) +ℕ_)
            ( ( inv
                ( coproduct-eq-is-finite
                  ( is-finite-intersection)
                  ( is-finite-intersection))) ∙
              ( ap
                ( _+ℕ
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
    number-of-elements-decidable-subtype-X :
      {l' : Level} → decidable-subtype l' X → ℕ
    number-of-elements-decidable-subtype-X R =
      number-of-elements-is-finite (is-finite-type-decidable-subtype R F)
    is-finite-coproduct-symmetric-difference :
      is-finite
        ( ( type-decidable-subtype
            ( symmetric-difference-decidable-subtype P Q)) +
          ( ( type-decidable-subtype
              ( intersection-decidable-subtype P Q)) +
            ( type-decidable-subtype
              ( intersection-decidable-subtype P Q))))
    is-finite-coproduct-symmetric-difference =
      is-finite-coproduct
        ( is-finite-type-decidable-subtype
          ( symmetric-difference-decidable-subtype P Q)
          ( F))
        ( is-finite-coproduct is-finite-intersection is-finite-intersection)
```
