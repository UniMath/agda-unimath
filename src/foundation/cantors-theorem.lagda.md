# Cantor's theorem

```agda
module foundation.cantors-diagonal-argument where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.propositions
```

</details>

## Idea

{{#concept "Cantor's theorem" Agda=theorem-Cantor WD="Cantor's theorem" WDID=Q474881}}
shows that there is [no](foundation-core.negation.md)
[surjective map](foundation.surjective-maps.md) from a type into its
[powerset](foundation.powersets.md).

```text
  ¬ (A ↠ 𝒫(A))
```

Cantor's theorem generalizes _Cantor's diagonal argument_, which shows that the
set of [infinite sequences](foundation.sequences.md) on a set with two distinct
elements is [uncountable](set-theory.uncountable-sets.md).

## Theorem

```agda
module _
  {l1 l2 : Level} {X : UU l1} (f : X → powerset l2 X)
  where

  map-theorem-Cantor : powerset l2 X
  map-theorem-Cantor x = neg-Prop (f x x)

  abstract
    not-in-image-map-theorem-Cantor :
      ¬ (fiber f map-theorem-Cantor)
    not-in-image-map-theorem-Cantor (x , α) =
      no-fixed-points-neg-Prop (f x x) (iff-eq (htpy-eq α x))

  abstract
    theorem-Cantor : ¬ (is-surjective f)
    theorem-Cantor H =
      ( apply-universal-property-trunc-Prop
        ( H map-theorem-Cantor)
        ( empty-Prop)
        ( not-in-image-map-theorem-Cantor))
```

## External links

- [Cantor's theorem](https://ncatlab.org/nlab/show/Cantor%27s+theorem) at $n$Lab
- [Cantor's theorem](https://en.wikipedia.org/wiki/Cantor%27s_theorem) at
  Wikipedia
- [Cantor's theorem](https://www.britannica.com/science/Cantors-theorem) at
  Britannica
