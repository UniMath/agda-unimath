# The image of a map

```agda
module univalent-combinatorics.image-of-maps where

open import foundation.images public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.fibers-of-maps
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (K : is-finite A)
  where

  abstract
    is-finite-codomain :
      is-surjective f → has-decidable-equality B → is-finite B
    is-finite-codomain H d =
      is-finite-base-is-finite-Σ-merely-inhabited
        ( is-set-has-decidable-equality d)
        ( H)
        ( is-finite-equiv' (equiv-total-fib f) K)
        ( λ b → is-finite-Σ K (λ a → is-finite-eq d))

abstract
  is-finite-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (K : is-finite A) →
    has-decidable-equality B → is-finite (im f)
  is-finite-im {f = f} K d =
    is-finite-codomain K
      ( is-surjective-map-unit-im f)
      ( λ x y →
        is-decidable-equiv
          ( extensionality-type-subtype' (λ u → trunc-Prop (fib f u)) x y)
          ( d (pr1 x) (pr1 y)))
```
