# Coproducts of null types

```agda
module orthogonal-factorization-systems.coproducts-null-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibers-of-maps
open import foundation.function-extensionality
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
open import foundation.retracts-of-maps
open import foundation.retracts-of-types
open import foundation.type-arithmetic-booleans
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-booleans
open import foundation.universal-property-equivalences
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-maps
open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.null-maps
open import orthogonal-factorization-systems.null-types
open import orthogonal-factorization-systems.orthogonal-maps
```

</details>

## Idea

The universe of `Y`-[null](orthogonal-factorization-systems.null-types.md) types
are closed under [coproducts](foundation.coproduct-types.md) if and only if the
[booleans](foundation.booleans.md) are `Y`-null.

## Properties

### The canonical map `A + B → bool` is `Y`-null if `A` and `B` are

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3}
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
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3}
  (is-null-bool : is-null Y bool)
  (is-null-A : is-null Y A)
  (is-null-B : is-null Y B)
  where

  is-null-coproduct-is-null-bool :
    is-null Y (A + B)
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
