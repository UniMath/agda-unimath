# Cauchy products of species of subuniverse

```agda
module species.cauchy-product-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

The Cauchy product of two species of types `S` and `T` on `X` is defined as

```md
  Σ (k : UU) (Σ (k' : UU) (Σ (e : k + k' ≃ X) S(k) × T(k')))
```

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  where

  cauchy-product-species-types : species-types l1 (lsuc l1 ⊔ l2 ⊔ l3)
  cauchy-product-species-types X =
    Σ ( binary-coproduct-Decomposition l1 l1 X)
      ( λ d →
        S (left-summand-binary-coproduct-Decomposition d) ×
        T (right-summand-binary-coproduct-Decomposition d))
```
