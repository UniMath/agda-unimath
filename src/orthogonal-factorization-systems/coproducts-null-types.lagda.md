# Coproducts of null types

```agda
module orthogonal-factorization-systems.coproducts-null-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.postcomposition-dependent-functions
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retracts-of-arrows
open import foundation.retracts-of-types
open import foundation.type-arithmetic-booleans
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-booleans
open import foundation.universal-property-equivalences
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.maps-local-at-maps
open import orthogonal-factorization-systems.null-maps
open import orthogonal-factorization-systems.null-types
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.types-local-at-maps

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The universe of `Y`-[null](orthogonal-factorization-systems.null-types.md) types
is closed under [coproducts](foundation.coproduct-types.md) if and only if the
[booleans](foundation.booleans.md) are `Y`-null.

## Properties

### The canonical map `A + B → bool` is `Y`-null if `A` and `B` are

```agda
module _
  {l1 l2 l3 : Level}
  (Y : UU l1) {A : UU l2} {B : UU l3}
  (is-null-A : is-null Y A)
  (is-null-B : is-null Y B)
  where

  abstract
    is-null-projection-bool-coproduct :
      is-null-map Y (projection-bool-coproduct {A = A} {B})
    is-null-projection-bool-coproduct =
      is-null-map-left-map-triangle Y
        ( λ where
          (inl _) → refl
          (inr _) → refl)
        ( is-null-map-pr1-is-null-family Y
          ( rec-bool (raise (l2 ⊔ l3) A) (raise (l2 ⊔ l3) B))
          ( λ where
            true →
              is-null-equiv-base (inv-compute-raise (l2 ⊔ l3) A) is-null-A
            false →
              is-null-equiv-base (inv-compute-raise (l2 ⊔ l3) B) is-null-B))
        ( is-null-map-map-equiv Y
          ( ( inv-equiv-Σ-bool-coproduct
              ( rec-bool (raise (l2 ⊔ l3) A) (raise (l2 ⊔ l3) B))) ∘e
            ( equiv-coproduct
              ( compute-raise (l2 ⊔ l3) A)
              ( compute-raise (l2 ⊔ l3) B))))
```

### If the booleans are `Y`-null then coproducts of `Y`-null types are `Y`-null

```agda
module _
  {l1 l2 l3 : Level}
  (Y : UU l1) {A : UU l2} {B : UU l3}
  (is-null-bool : is-null Y bool)
  (is-null-A : is-null Y A)
  (is-null-B : is-null Y B)
  where

  is-null-coproduct-is-null-bool : is-null Y (A + B)
  is-null-coproduct-is-null-bool =
    is-null-is-orthogonal-terminal-maps
      ( is-orthogonal-right-comp
        ( terminal-map Y)
        ( projection-bool-coproduct)
        ( terminal-map bool)
        ( is-orthogonal-terminal-maps-is-null is-null-bool)
        ( is-orthogonal-terminal-map-is-null-map Y
          ( projection-bool-coproduct)
          ( is-null-projection-bool-coproduct Y is-null-A is-null-B)))
```

### If null types are closed under coproducts, then the booleans are null

```agda
abstract
  is-null-bool-is-null-coproduct :
    {l1 : Level} {Y : UU l1} →
    ( {l2 l3 : Level} {A : UU l2} {B : UU l3} →
      is-null Y A → is-null Y B → is-null Y (A + B)) →
    is-null Y bool
  is-null-bool-is-null-coproduct {Y = Y} H =
    is-null-equiv-base
      ( equiv-bool-coproduct-unit)
      ( H ( is-null-is-contr Y is-contr-unit)
          ( is-null-is-contr Y is-contr-unit))
```

### If the booleans are `Y`-null then all standard finite types are `Y`-null

```agda
module _
  {l1 : Level} (Y : UU l1)
  (is-null-bool : is-null Y bool)
  where

  abstract
    is-null-empty : is-null Y empty
    is-null-empty =
      is-null-equiv-base
        ( equiv-is-empty id neq-true-false-bool)
        ( is-null-Id is-null-bool true false)

    is-null-is-empty :
      {l2 : Level} {A : UU l2} →
      is-empty A →
      is-null Y A
    is-null-is-empty is-empty-A =
      is-null-equiv-base (equiv-is-empty is-empty-A id) is-null-empty

abstract
  is-null-Fin-is-null-bool :
    {l1 : Level} (Y : UU l1) →
    is-null Y bool →
    (n : ℕ) →
    is-null Y (Fin n)
  is-null-Fin-is-null-bool Y is-null-bool =
    ind-ℕ
      ( is-null-empty Y is-null-bool)
      ( λ n is-null-Fin-n →
        is-null-coproduct-is-null-bool
          ( Y)
          ( is-null-bool)
          ( is-null-Fin-n)
          ( is-null-is-contr Y is-contr-unit))
```

### If the booleans are `Y`-null then all finite types are `Y`-null

```agda
abstract
  is-null-is-finite-is-null-bool :
    {l1 l2 : Level} (Y : UU l1) {X : UU l2} →
    is-null Y bool →
    is-finite X →
    is-null Y X
  is-null-is-finite-is-null-bool Y {X = X} is-null-bool is-finite-X =
    apply-universal-property-trunc-Prop
      ( is-finite-X)
      ( is-null-Prop Y X)
      ( λ (n , e) →
        is-null-equiv-base
          ( inv-equiv e)
          ( is-null-Fin-is-null-bool Y is-null-bool n))

  is-null-type-Finite-Type-is-null-bool :
    {l1 l2 : Level} (Y : UU l1) →
    is-null Y bool →
    (X : Finite-Type l2) →
    is-null Y (type-Finite-Type X)
  is-null-type-Finite-Type-is-null-bool Y is-null-bool X =
    is-null-is-finite-is-null-bool Y
      ( is-null-bool)
      ( is-finite-type-Finite-Type X)
```
