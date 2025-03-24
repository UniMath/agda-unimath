# Dirichlet products of species of types

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.dirichlet-products-species-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.product-decompositions
open import foundation.universe-levels

open import species.species-of-types funext univalence
```

</details>

## Idea

The Dirichlet product of two species of types `S` and `T` on `X` is defined as

```text
  Σ (k : UU) (Σ (k' : UU) (Σ (e : k × k' ≃ X) S(k) × T(k')))
```

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  where

  dirichlet-product-species-types : species-types l1 (lsuc l1 ⊔ l2 ⊔ l3)
  dirichlet-product-species-types X =
    Σ ( binary-product-Decomposition l1 l1 X)
      ( λ d →
        S (left-summand-binary-product-Decomposition d) ×
        T (right-summand-binary-product-Decomposition d))
```
