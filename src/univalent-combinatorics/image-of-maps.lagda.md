# The image of a map

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.image-of-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation.images funext univalence truncations public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality funext univalence truncations
open import foundation.decidable-types funext univalence truncations
open import foundation.fibers-of-maps funext
open import foundation.propositional-truncations funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.surjective-maps funext univalence truncations
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types funext univalence truncations
open import univalent-combinatorics.equality-finite-types funext univalence truncations
open import univalent-combinatorics.finite-types funext univalence truncations
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
        ( is-finite-equiv' (equiv-total-fiber f) K)
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
          ( extensionality-type-subtype' (λ u → trunc-Prop (fiber f u)) x y)
          ( d (pr1 x) (pr1 y)))
```
