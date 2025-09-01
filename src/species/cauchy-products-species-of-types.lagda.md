# Cauchy products of species of types

```agda
module species.cauchy-products-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

The
{{#concept "Cauchy product" Disambiguation="of species of types" Agda=cauchy-product-species-types}}
of two [species of types](species.species-of-types.md) `S` and `T` on `X` is
defined as

```text
  Σ (k : UU) (Σ (k' : UU) (Σ (e : k + k' ≃ X) S(k) × T(k'))).
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
