# Cauchy series of species of types

```agda
module species.cauchy-series-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.postcomposition-functions
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

In classical mathematics, the _Cauchy series_ of a
[species](species.finite-species.md) (of
[finite types](univalent-combinatorics.finite-types.md)) `S` is the formal
series in `x`:

```text
  Σ (n : ℕ) (|S({1,...,n})| x^n / n!)
```

The categorified version of this series is:

```text
  Σ (F : Finite-Type), S(F) × (F → X).
```

Hence, we can generalize to
{{#concept "Cauchy series" Disambiguation="of species of types" Agda=cauchy-series-species-types}}
of any [species of types](species.species-of-types.md) `S` with the following
definition:

```text
  Σ (U : UU), S(U) × (U → X).
```

## Definition

```agda
cauchy-series-species-types :
  {l1 l2 l3 : Level} → species-types l1 l2 → UU l3 → UU (lsuc l1 ⊔ l2 ⊔ l3)
cauchy-series-species-types {l1} S X = Σ (UU l1) (λ U → S U × (U → X))
```

## Properties

### Equivalent species of types have equivalent Cauchy series

```agda
module _
  {l1 l2 l3 l4 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  (f : (F : UU l1) → (S F ≃ T F))
  (X : UU l4)
  where

  equiv-cauchy-series-equiv-species-types :
    cauchy-series-species-types S X ≃ cauchy-series-species-types T X
  equiv-cauchy-series-equiv-species-types =
    equiv-tot (λ X → equiv-product-left (f X))
```

### Cauchy series of types are equivalence invariant

```agda
module _
  {l1 l2 l3 l4 : Level}
  (S : species-types l1 l2)
  {X : UU l3} {Y : UU l4}
  (e : X ≃ Y)
  where

  equiv-cauchy-series-species-types :
    cauchy-series-species-types S X ≃ cauchy-series-species-types S Y
  equiv-cauchy-series-species-types =
    equiv-tot (λ F → equiv-product-right (equiv-postcomp F e))
```
