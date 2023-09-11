# Cantor's diagonal argument

```agda
module foundation.cantors-diagonal-argument where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-extensionality
open import foundation-core.propositions
```

</details>

## Idea

Cantor's diagonal argument is used to show that there is no surjective map from
a type into the type of its subtypes.

## Theorem

```agda
map-cantor :
  {l1 l2 : Level} (X : UU l1) (f : X → (X → Prop l2)) → (X → Prop l2)
map-cantor X f x = neg-Prop (f x x)

abstract
  not-in-image-map-cantor :
    {l1 l2 : Level} (X : UU l1) (f : X → (X → Prop l2)) →
    ( t : fiber f (map-cantor X f)) → empty
  not-in-image-map-cantor X f (pair x α) =
    no-fixed-points-neg-Prop (f x x) (iff-eq (htpy-eq α x))

abstract
  cantor :
    {l1 l2 : Level} (X : UU l1) (f : X → X → Prop l2) → ¬ (is-surjective f)
  cantor X f H =
    ( apply-universal-property-trunc-Prop
      ( H (map-cantor X f))
      ( empty-Prop)
      ( not-in-image-map-cantor X f))
```
