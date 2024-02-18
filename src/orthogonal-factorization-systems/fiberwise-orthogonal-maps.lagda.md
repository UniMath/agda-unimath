# Fiberwise orthogonal maps

```agda
module orthogonal-factorization-systems.fiberwise-orthogonal-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibered-maps
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.type-arithmetic-dependent-function-types
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.lifting-structures-on-squares
open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The map `f : A → B` is said to be
{{#concept "fiberwise orthogonal" Disambiguation="maps of types" Agda=is-orthogonal}}
to `g : X → Y` if every [base change](foundation.cartesian-morphisms-arrows.md)
of `f` is [orthogonal](orthogonal-factorization-systems.md) to `g`.

More concretely, for every [pullback](foundation-core.pullbacks.md) square

```text
    A' -------> A
    | ⌟         |
  f'|           | f
    ∨           ∨
    B' -------> B
```

The exponential square

```text
              - ∘ f'
      B' → X -------> A' → X
        |              |
  g ∘ - |              | g ∘ -
        V              V
      B' → Y -------> A' → Y
              - ∘ f'
```

is also a pullback.

## Definitions

### The universal property of fiberwise orthogonal maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  universal-property-fiberwise-orthogonal-maps : UUω
  universal-property-fiberwise-orthogonal-maps =
    {l5 l6 : Level} {A' : UU l5} {B' : UU l6}
    (f' : A' → B') (α : cartesian-hom-arrow f' f) →
    universal-property-orthogonal-maps f' g
```

## Properties
