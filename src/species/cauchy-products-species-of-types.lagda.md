# Cauchy products of species of types

```agda
open import foundation.function-extensionality-axiom

module
  species.cauchy-products-species-of-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.coproduct-decompositions funext
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import species.species-of-types funext
```

</details>

## Idea

The Cauchy product of two species of types `S` and `T` on `X` is defined as

```text
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
