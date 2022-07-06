# Symmetric difference of finite subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.symmetric-difference where

open import foundation.symmetric-difference public

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  (mul-ℕ; left-unit-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.coproduct-types using (coprod)
open import foundation.decidable-subtypes using
  ( decidable-subtype; type-decidable-subtype)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equivalences using (inv-equiv)
open import foundation.identity-types using (Id; _∙_; refl; ap; tr; inv)
open import foundation.intersection using (intersection-decidable-subtype)
open import foundation.mere-equivalences using (transitive-mere-equiv)
open import foundation.propositional-truncations using (unit-trunc-Prop)
open import foundation.subtypes using (subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.xor using (xor-Prop; xor-decidable-Prop)

open import univalent-combinatorics.coproduct-types using
  ( coprod-eq-is-finite; is-finite-coprod)
open import univalent-combinatorics.decidable-subtypes using ( is-finite-decidable-subtype)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; has-cardinality-type-UU-Fin-Level; number-of-elements-is-finite;
    is-finite; is-finite-has-cardinality; number-of-elements-has-finite-cardinality;
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
        ( number-of-elements-is-finite (is-finite-decidable-subtype P F))        
        ( number-of-elements-is-finite (is-finite-decidable-subtype Q F)))
      ( add-ℕ
        ( number-of-elements-is-finite
          ( is-finite-decidable-subtype (symmetric-difference-decidable-subtype P Q) F))
        ( mul-ℕ
          2
          ( number-of-elements-is-finite
            ( is-finite-decidable-subtype
              ( intersection-decidable-subtype P Q)
              ( F)))))
  eq-symmetric-difference =
    ( ( coprod-eq-is-finite
      ( is-finite-decidable-subtype P F)
      ( is-finite-decidable-subtype Q F))) ∙
      ( ( ap
        ( number-of-elements-has-finite-cardinality)
        ( all-elements-equal-has-finite-cardinality
          ( has-finite-cardinality-is-finite
            ( is-finite-coprod
              ( is-finite-decidable-subtype P F)
              ( is-finite-decidable-subtype Q F)))
          ( pair
            ( number-of-elements-is-finite is-finite-coprod-symmetric-difference)
            ( transitive-mere-equiv
              ( mere-equiv-has-finite-cardinality
                ( has-finite-cardinality-is-finite is-finite-coprod-symmetric-difference))
              ( unit-trunc-Prop (inv-equiv (equiv-symmetric-difference P Q))))))) ∙
        ( inv
          ( coprod-eq-is-finite
            ( is-finite-decidable-subtype (symmetric-difference-decidable-subtype P Q) F)
            ( is-finite-coprod is-finite-intersection is-finite-intersection)) ∙
          ( ap
            ( λ n →
              add-ℕ
                ( number-of-elements-decidable-subtype-X
                  ( symmetric-difference-decidable-subtype P Q))
                ( n))
            ( ( inv
              ( coprod-eq-is-finite is-finite-intersection is-finite-intersection)) ∙
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
      is-finite-decidable-subtype (intersection-decidable-subtype P Q) F
    number-of-elements-decidable-subtype-X : {l' : Level} →
      (decidable-subtype l' X) → ℕ
    number-of-elements-decidable-subtype-X R =
      number-of-elements-is-finite (is-finite-decidable-subtype R F)
    is-finite-coprod-symmetric-difference :
      is-finite
        ( coprod
          ( type-decidable-subtype
            ( symmetric-difference-decidable-subtype P Q))
          ( coprod
            ( type-decidable-subtype
              ( intersection-decidable-subtype P Q))
            ( type-decidable-subtype
              ( intersection-decidable-subtype P Q))))
    is-finite-coprod-symmetric-difference =
      is-finite-coprod
        ( is-finite-decidable-subtype (symmetric-difference-decidable-subtype P Q) F)
        ( is-finite-coprod is-finite-intersection is-finite-intersection)
