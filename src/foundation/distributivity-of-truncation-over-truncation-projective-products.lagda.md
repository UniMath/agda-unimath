# Distributivity of truncation over truncation-projective products

```agda
module foundation.distributivity-of-truncation-over-truncation-projective-products where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.surjective-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncation-projective-types
open import foundation.truncations
open import foundation.universe-levels
```

</details>

## Idea

For a $k$-[projective](foundation.truncation-projective-types.md) type $X$,
[postcomposition](foundation.postcomposition-functions.md) by the unit map into
the $(k-1)$-[truncation](foundation.truncations.md) is
[surjective](foundation.surjective-maps.md), and therefore the induced
distributivity map

$$
  ║ (x : X) → A(x) ║_{k-1} → ((x : X) → ║ A(x) ║_{k-1})
$$

is surjective.

## Properties

### Distributivity of truncation over 𝑘-projective types

```agda
module _
  {l1 l2 : Level} (k : ℕ) (X : UU l1) (A : UU l2)
  where

  is-surjective-postcomp-unit-trunc-is-trunc-projective-Level :
    is-trunc-projective-Level l2 l2 k X →
    is-surjective
      ( postcomp
        ( X)
        ( unit-trunc {k = truncation-level-minus-one-ℕ k} {A = A}))
  is-surjective-postcomp-unit-trunc-is-trunc-projective-Level H =
    H ( A)
      ( type-trunc (truncation-level-minus-one-ℕ k) A ,
        is-trunc-succ-is-trunc
          ( truncation-level-minus-one-ℕ k)
          ( is-trunc-type-trunc {k = truncation-level-minus-one-ℕ k} {A = A}))
      ( unit-trunc {k = truncation-level-minus-one-ℕ k} {A = A} ,
        is-connected-map-unit-trunc (truncation-level-minus-one-ℕ k))

  is-surjective-map-distributive-trunc-function-type-is-trunc-projective-Level :
    is-trunc-projective-Level l2 l2 k X →
    is-surjective
      ( map-distributive-trunc-function-type
        ( truncation-level-minus-one-ℕ k)
        ( X)
        ( A))
  is-surjective-map-distributive-trunc-function-type-is-trunc-projective-Level
    H =
    is-surjective-right-map-triangle
      ( postcomp
        ( X)
        ( unit-trunc {k = truncation-level-minus-one-ℕ k} {A = A}))
      ( map-distributive-trunc-function-type
        ( truncation-level-minus-one-ℕ k)
        ( X)
        ( A))
      ( unit-trunc {k = truncation-level-minus-one-ℕ k})
      ( λ f →
        inv
          ( eq-htpy
            ( compute-distributive-trunc-function-type
              ( truncation-level-minus-one-ℕ k)
              ( f))))
      ( is-surjective-postcomp-unit-trunc-is-trunc-projective-Level H)

is-surjective-postcomp-unit-trunc-is-trunc-projective :
  {l1 l2 : Level} (k : ℕ) {X : UU l1} {A : UU l2} →
  is-trunc-projective k X →
  is-surjective
    ( postcomp
      ( X)
      ( unit-trunc {k = truncation-level-minus-one-ℕ k} {A = A}))
is-surjective-postcomp-unit-trunc-is-trunc-projective k {X} {A} H =
  is-surjective-postcomp-unit-trunc-is-trunc-projective-Level k X A H

is-surjective-map-distributive-trunc-function-type-is-trunc-projective :
  {l1 l2 : Level} (k : ℕ) {X : UU l1} {A : UU l2} →
  is-trunc-projective k X →
  is-surjective
    ( map-distributive-trunc-function-type
      ( truncation-level-minus-one-ℕ k)
      ( X)
      ( A))
is-surjective-map-distributive-trunc-function-type-is-trunc-projective
  k {X} {A} H =
  is-surjective-map-distributive-trunc-function-type-is-trunc-projective-Level
    k X A H
```

## See also

- [Distributivity of set-truncation over projective products](foundation.distributivity-of-set-truncation-over-projective-products.md)
