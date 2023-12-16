# Orthogonal maps

```agda
module orthogonal-factorization-systems.orthogonal-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibered-maps
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.universal-property-pullbacks
open import foundation.universe-levels

open import orthogonal-factorization-systems.lifting-squares
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The map `f : A → B` is said to be
{{#concept "orthogonal" Disambiguation="maps of types" Agda=is-orthogonal}} to
`g : X → Y` if any of the following equivalent definitions hold

1. Their [pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is an
   equivalence.
2. There is a unique
   [lifting operation](orthogonal-factorization-systems.lifting-operations.md)
   between `f` and `g`.
3. The following is a [pullback square](foundation.pullback-squares.md):
   ```text
                - ∘ f
         B → X -------> A → X
           |              |
     g ∘ - |              | g ∘ -
           V              V
         B → Y -------> A → Y.
                - ∘ f
   ```

If `f` is orthogonal to `g`, we say that `f` is
{{#concept "left orthogonal" Disambiguation="maps of types" Agda=is-left-orthogonal}}
to `g` and `g` is
{{#concept "right orthogonal" Disambiguation="maps of types" Agda=is-right-orthogonal}}
to `f`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-orthogonal = is-equiv (pullback-hom f g)

  _⊥_ = is-orthogonal

  is-property-is-orthogonal : is-prop is-orthogonal
  is-property-is-orthogonal = is-property-is-equiv (pullback-hom f g)

  is-orthogonal-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-orthogonal-Prop = is-orthogonal
  pr2 is-orthogonal-Prop = is-property-is-orthogonal
```

A term of `is-right-orthogonal f g` asserts that `g` is right orthogonal to `f`.

```agda
  is-right-orthogonal : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-right-orthogonal = is-orthogonal
```

A term of `is-left-orthogonal f g` asserts that `g` is left orthogonal to `f`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-left-orthogonal : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-left-orthogonal = is-orthogonal g f
```

### The universal property of orthogonal maps

The maps `f` and `g` are orthogonal if and only if the square

```text
             - ∘ f
      B → X -------> A → X
        |              |
  g ∘ - |              | g ∘ -
        V              V
      B → Y -------> A → Y.
             - ∘ f
```

is a pullback.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  universal-property-orthogonal-maps : UUω
  universal-property-orthogonal-maps =
    universal-property-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
```

## Properties

### Being orthogonal means that the type of lifting squares is contractible

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  unique-lifting-squares-is-orthogonal :
    is-orthogonal f g →
    (h : fibered-map f g) →
    is-contr (lifting-square-fibered-map f g h)
  unique-lifting-squares-is-orthogonal H h =
    is-contr-equiv
      ( fiber (pullback-hom f g) h)
      ( compute-fiber-pullback-hom f g h)
      ( is-contr-map-is-equiv H h)

  is-orthogonal-unique-lifting-squares :
    ( (h : fibered-map f g) → is-contr (lifting-square-fibered-map f g h)) →
    is-orthogonal f g
  is-orthogonal-unique-lifting-squares H =
    is-equiv-is-contr-map
      ( λ h →
        is-contr-equiv'
          ( lifting-square-fibered-map f g h)
          ( compute-fiber-pullback-hom f g h)
          ( H h))
```

### Being orthogonal means satisfying the universal property of being orthogonal

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  universal-property-orthogonal-maps-is-orthogonal :
    is-orthogonal f g → universal-property-orthogonal-maps f g
  universal-property-orthogonal-maps-is-orthogonal G =
    universal-property-pullback-is-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
      ( is-equiv-right-factor
        ( map-fibered-map-type-standard-pullback-hom f g)
        ( gap
          ( precomp f Y)
          ( postcomp A g)
          ( cone-pullback-hom' f g))
        ( is-equiv-map-equiv (equiv-fibered-map-type-standard-pullback-hom f g))
        ( G))

  is-orthogonal-universal-property-orthogonal-maps :
    universal-property-orthogonal-maps f g → is-orthogonal f g
  is-orthogonal-universal-property-orthogonal-maps G =
    is-equiv-comp
      ( map-fibered-map-type-standard-pullback-hom f g)
      ( gap
        ( precomp f Y)
        ( postcomp A g)
        ( cone-pullback-hom' f g))
      ( is-pullback-universal-property-pullback
        ( precomp f Y)
        ( postcomp A g)
        ( cone-pullback-hom' f g)
        ( G))
      ( is-equiv-map-equiv (equiv-fibered-map-type-standard-pullback-hom f g))
```

### Right orthogonal maps are closed under composition and have the right cancellation property

Given two composable maps `h` after `g`, if `h` is right orthogonal to `f` then
`g` is right orthogonal to `f` if and only if `h ∘ g` is.

**Proof:** By the universal property of orthogonal maps, the top square in the
below diagram is a pullback precisely when `g` is right orthogonal to `f`:

```text
             - ∘ f
      B → X -------> A → X
        |              |
  g ∘ - |              | g ∘ -
        V              V
      B → Y -------> A → Y
        | ⌟            |
  h ∘ - |              | h ∘ -
        V              V
      B → Z -------> A → Z.
             - ∘ f
```

so the result is an instance of the vertical pasting property for pullbacks.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {Z : UU l5}
  (f : A → B) (g : X → Y) (h : Y → Z)
  where

  up-orthogonal-right-comp :
    universal-property-orthogonal-maps f h →
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps f (h ∘ g)
  up-orthogonal-right-comp =
    up-pullback-rectangle-up-pullback-top
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom' f h)
      ( cone-pullback-hom' f g)

  is-orthogonal-right-comp :
    is-orthogonal f h → is-orthogonal f g → is-orthogonal f (h ∘ g)
  is-orthogonal-right-comp H G =
    is-orthogonal-universal-property-orthogonal-maps f (h ∘ g)
      ( up-orthogonal-right-comp
        ( universal-property-orthogonal-maps-is-orthogonal f h H)
        ( universal-property-orthogonal-maps-is-orthogonal f g G))

  up-orthogonal-right-right-factor :
    universal-property-orthogonal-maps f h →
    universal-property-orthogonal-maps f (h ∘ g) →
    universal-property-orthogonal-maps f g
  up-orthogonal-right-right-factor =
    up-pullback-top-up-pullback-rectangle
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom' f h)
      ( cone-pullback-hom' f g)

  is-orthogonal-right-right-factor :
    is-orthogonal f h → is-orthogonal f (h ∘ g) → is-orthogonal f g
  is-orthogonal-right-right-factor H HG =
    is-orthogonal-universal-property-orthogonal-maps f g
      ( up-orthogonal-right-right-factor
        ( universal-property-orthogonal-maps-is-orthogonal f h H)
        ( universal-property-orthogonal-maps-is-orthogonal f (h ∘ g) HG))
```

### Left orthogonal maps are closed under composition and have the left cancellation property

Given two composable maps `h` after `f`, if `f` is left orthogonal to `g` then
`h` is left orthogonal to `g` if and only if `h ∘ f` is.

**Proof:** By the universal property of orthogonal maps, the right square in the
below diagram is a pullback precisely when `f` is left orthogonal to `g`:

```text
             - ∘ h          - ∘ f
      C → X -------> B → X -------> A → X
        |              | ⌟            |
  g ∘ - |              |              | g ∘ -
        V              V              V
      C → Y -------> B → Y -------> A → Y
             - ∘ h          - ∘ f
```

so the result is an instance of the horizontal pasting property for pullbacks.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {C : UU l5}
  (f : A → B) (h : B → C) (g : X → Y)
  where

  up-orthogonal-left-comp :
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps h g →
    universal-property-orthogonal-maps (h ∘ f) g
  up-orthogonal-left-comp =
    up-pullback-rectangle-up-pullback-left-square
      ( precomp h Y)
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
      ( cone-pullback-hom' h g)

  is-orthogonal-left-comp :
    is-orthogonal f g → is-orthogonal h g → is-orthogonal (h ∘ f) g
  is-orthogonal-left-comp F H =
    is-orthogonal-universal-property-orthogonal-maps (h ∘ f) g
      ( up-orthogonal-left-comp
        ( universal-property-orthogonal-maps-is-orthogonal f g F)
        ( universal-property-orthogonal-maps-is-orthogonal h g H))

  up-orthogonal-left-left-factor :
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps (h ∘ f) g →
    universal-property-orthogonal-maps h g
  up-orthogonal-left-left-factor =
    up-pullback-left-square-up-pullback-rectangle
      ( precomp h Y)
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
      ( cone-pullback-hom' h g)

  is-orthogonal-left-left-factor :
    is-orthogonal f g → is-orthogonal (h ∘ f) g → is-orthogonal h g
  is-orthogonal-left-left-factor F HF =
    is-orthogonal-universal-property-orthogonal-maps h g
      ( up-orthogonal-left-left-factor
        ( universal-property-orthogonal-maps-is-orthogonal f g F)
        ( universal-property-orthogonal-maps-is-orthogonal (h ∘ f) g HF))
```
