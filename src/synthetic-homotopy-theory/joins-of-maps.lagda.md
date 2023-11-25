# Joins of maps

```agda
module synthetic-homotopy-theory.joins-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.pullbacks
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Consider two maps `f : A → X` and `g : B → X` with a common codomain. The
**join** `f * g` of `f` and `g` is defined as the
[cogap map](synthetic-homotopy-theory.pushouts.md) of the
[pullback square](foundation.pullbacks.md)

```text
             π₂
   A ×_X B -----> B
     | ⌟          |
  π₁ |            | g
     V            V
     A ---------> X.
           f
```

We often write `A *_X B` for the domain of the fiberwise join. In other words,
the cogap map of any cartesian square

```text
        i
    A -----> X
    | ⌟      |
  f |        | g
    V        V
    B -----> Y
        i
```

is the join of `i` and `g`. The join of maps is also called the **fiberwise
join** because for each `x : X` we have an
[equivalence](foundation-core.equivalences.md)

```text
  fiber (f * g) x ≃ (fiber f x) * (fiber g x)
```

from the [fiber](foundation-core.fibers-of-maps.md) of `f * g` to the
[join](synthetic-homotopy-theory.joins-of-types.md) of the fibers of `f` and
`g`. In other words, there is a
[commuting triangle](foundation.commuting-triangles-of-maps.md)

```text
            ≃
   A *_X B --> Σ (x : X), (fiber f x) * (fiber g x)
        \       /
         \     /
          \   /
           V V
            X.
```

in which the top map is an equivalence. The join of maps is related to the
[pushout-product](synthetic-homotopy-theory.pushout-products.md), because it
fits in a [pullback diagram](foundation.pullback-squares.md)

```text
      A *_X B ------> (X × B) ⊔_{A × B} (A × X)
        | ⌟                   |
  f * g |                     | f □ g
        V                     V
        X ----------------> X × X.
                 Δ
```

A second way in which the pushout-product is related to the join of maps, is
that there is a commuting triangle

```text
                              ≃
  (X × B) ⊔_{A × B} (A × X) ----> (A × Y) *_{X × Y} (X × B)
                        \           /
                   f □ g \         / (f × id) * (id × g)
                          \       /
                           V     V
                            X × Y
```

This is an immediate consequence of the fact that the ambient square of the
pushout-product is cartesian, and therefore its cogap map is the join of the two
terminal maps in the square.

## Definitions

### The join of maps

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X) (g : B → X)
  where

  domain-join-maps : UU (l1 ⊔ l2 ⊔ l3)
  domain-join-maps =
    pushout
      ( vertical-map-standard-pullback {f = f} {g = g})
      ( horizontal-map-standard-pullback {f = f} {g = g})

  cocone-join-maps :
    cocone
      ( vertical-map-standard-pullback {f = f} {g = g})
      ( horizontal-map-standard-pullback {f = f} {g = g})
      ( X)
  pr1 cocone-join-maps = f
  pr1 (pr2 cocone-join-maps) = g
  pr2 (pr2 cocone-join-maps) = coherence-square-standard-pullback

  abstract
    uniqueness-join-maps :
      is-contr
        ( Σ ( domain-join-maps → X)
            ( λ h →
              htpy-cocone
                ( vertical-map-standard-pullback)
                ( horizontal-map-standard-pullback)
                ( cocone-map
                  ( vertical-map-standard-pullback)
                  ( horizontal-map-standard-pullback)
                  ( cocone-pushout
                    ( vertical-map-standard-pullback)
                    ( horizontal-map-standard-pullback))
                  ( h))
                ( cocone-join-maps)))
    uniqueness-join-maps =
      uniqueness-map-universal-property-pushout
        ( vertical-map-standard-pullback)
        ( horizontal-map-standard-pullback)
        ( cocone-pushout
          ( vertical-map-standard-pullback)
          ( horizontal-map-standard-pullback))
        ( up-pushout _ _)
        ( cocone-join-maps)

  abstract
    join-maps : domain-join-maps → X
    join-maps = pr1 (center uniqueness-join-maps)

    compute-inl-join-maps : join-maps ∘ inl-pushout _ _ ~ f
    compute-inl-join-maps = pr1 (pr2 (center uniqueness-join-maps))

    compute-inr-join-maps : join-maps ∘ inr-pushout _ _ ~ g
    compute-inr-join-maps = pr1 (pr2 (pr2 (center uniqueness-join-maps)))

    compute-glue-join-maps :
      statement-coherence-htpy-cocone
        ( vertical-map-standard-pullback)
        ( horizontal-map-standard-pullback)
        ( cocone-map
          ( vertical-map-standard-pullback)
          ( horizontal-map-standard-pullback)
          ( cocone-pushout
            ( vertical-map-standard-pullback)
            ( horizontal-map-standard-pullback))
          ( join-maps))
        ( cocone-join-maps)
        ( compute-inl-join-maps)
        ( compute-inr-join-maps)
    compute-glue-join-maps =
      pr2 (pr2 (pr2 (center uniqueness-join-maps)))
```

## External links

- [Join of maps](https://ncatlab.org/nlab/show/join+of+maps) at the $n$Lab
