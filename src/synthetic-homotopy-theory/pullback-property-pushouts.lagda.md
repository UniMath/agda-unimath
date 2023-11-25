# The pullback property of pushouts

```agda
module synthetic-homotopy-theory.pullback-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.spans
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

The
[universal property of the pushout](synthetic-homotopy-theory.universal-property-pushouts.md)
of a span `S` can also be stated as a
[pullback property](foundation-core.universal-property-pullbacks.md): a cocone
`c ≐ (i , j , H)` with vertex `X` satisfies the universal property of the
pushout of `S` if and only if the square

```text
  Y^X -----> Y^B
   | ⌟        |
   |          |
   V          V
  Y^A -----> Y^S
```

is a [pullback square](foundation.pullback-squares.md) for every type `Y`.
Below, we first define the [cone](foundation.cones-over-cospans.md) of this
[commuting square](foundation.commuting-squares-of-maps.md), and then we
introduce the type `pullback-property-pushout`, which states that the above
square is a [pullback](foundation-core.universal-property-pullbacks.md).

## Definition

### The pullback property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3)
  {X : UU l4} (c : cocone-span s X)
  where

  cone-pullback-property-pushout :
    {l : Level} (Y : UU l) →
    cone (_∘ left-map-span s) (_∘ right-map-span s) (X → Y)
  pr1 (cone-pullback-property-pushout Y) =
    precomp (horizontal-map-cocone-span s c) Y
  pr1 (pr2 (cone-pullback-property-pushout Y)) =
    precomp (vertical-map-cocone-span s c) Y
  pr2 (pr2 (cone-pullback-property-pushout Y)) =
    precomp-coherence-square-maps
      ( right-map-span s)
      ( left-map-span s)
      ( vertical-map-cocone-span s c)
      ( horizontal-map-cocone-span s c)
      ( coherence-square-cocone-span s c)
      ( Y)

  pullback-property-pushout : UUω
  pullback-property-pushout =
    {l : Level} (Y : UU l) →
    is-pullback
      ( precomp (left-map-span s) Y)
      ( precomp (right-map-span s) Y)
      ( cone-pullback-property-pushout Y)
```
