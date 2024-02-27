# Standard pullbacks

```agda
module foundation.standard-pullbacks where

open import foundation-core.standard-pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-function-types
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.postcomposition-functions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

Given a [cospan of types](foundation.cospans.md)

```text
  f : A → X ← B : g,
```

we can form the
{{#concept "standard pullback" Disambiguation="types" Agda=standard-pullback}}
`A ×_X B` satisfying
[the universal property of the pullback](foundation-core.universal-property-pullbacks.md)
of the cospan, completing the diagram

```text
  A ×_X B ------> B
     | ⌟          |
     |            | g
     |            |
     v            v
     A ---------> X.
           f
```

The standard pullback consists of [pairs](foundation.dependent-pair-types.md)
`a : A` and `b : B` such that `f a ＝ g b` agree

```text
  A ×_X B := Σ (a : A) (b : B), (f a ＝ g b),
```

thus the standard [cone](foundation.cones-over-cospan-diagrams.md) consists of
the canonical projections.

## Properties

### The equivalence on standard pullbacks induced by parallel cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  map-equiv-standard-pullback-htpy :
    standard-pullback f' g' → standard-pullback f g
  map-equiv-standard-pullback-htpy =
    tot (λ a → tot (λ b → concat' (f a) (inv (Hg b)) ∘ concat (Hf a) (g' b)))

  abstract
    is-equiv-map-equiv-standard-pullback-htpy :
      is-equiv map-equiv-standard-pullback-htpy
    is-equiv-map-equiv-standard-pullback-htpy =
      is-equiv-tot-is-fiberwise-equiv
        ( λ a →
          is-equiv-tot-is-fiberwise-equiv
            ( λ b →
              is-equiv-comp
                ( concat' (f a) (inv (Hg b)))
                ( concat (Hf a) (g' b))
                ( is-equiv-concat (Hf a) (g' b))
                ( is-equiv-concat' (f a) (inv (Hg b)))))

  equiv-standard-pullback-htpy :
    standard-pullback f' g' ≃ standard-pullback f g
  pr1 equiv-standard-pullback-htpy = map-equiv-standard-pullback-htpy
  pr2 equiv-standard-pullback-htpy = is-equiv-map-equiv-standard-pullback-htpy
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
