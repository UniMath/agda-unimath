# The pullback-hom

```agda
module orthogonal-factorization-systems.pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibered-maps
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import orthogonal-factorization-systems.lifting-squares
```

</details>

## Idea

Given a pair of maps `f : A → B` and `g : X → Y`, there is a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
          - ∘ f
    B → X ----> A → X
      |           |
g ∘ - |           | g ∘ -
      V           V
    B → Y ----> A → Y.
          - ∘ f
```

The **pullback-hom** of `f` and `g`, `f ⋔ g`, is the comparison map from `B → X`
to the [pullback](foundation.pullbacks.md) of the
[cospan](foundation.cospans.md):

```text
      ∙ ------> A → X
      |  ⌟        |
      |           | g ∘ -
      V           V
    B → Y ----> A → Y.
          - ∘ f
```

This pullback type can be understood as the type of
[fibered maps](foundation.fibered-maps.md) from `f` to `g`, i.e.
[commuting squares](foundation-core.commuting-squares-of-maps.md) where the
vertical maps are `f` and `g`.

## Definitions

### The codomain of the pullback-hom

```agda
type-standard-pullback-hom :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
type-standard-pullback-hom {A = A} {Y = Y} f g =
  standard-pullback (precomp f Y) (postcomp A g)
```

#### The canonical pullback-hom type is equivalent to the type of fibered maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  equiv-fibered-map-type-standard-pullback-hom :
    type-standard-pullback-hom f g ≃ fibered-map f g
  equiv-fibered-map-type-standard-pullback-hom =
    equiv-tot (λ _ → equiv-tot (λ _ → equiv-funext))

  equiv-type-standard-pullback-hom-fibered-map :
    fibered-map f g ≃ type-standard-pullback-hom f g
  equiv-type-standard-pullback-hom-fibered-map =
    inv-equiv equiv-fibered-map-type-standard-pullback-hom

  map-fibered-map-type-standard-pullback-hom :
    type-standard-pullback-hom f g → fibered-map f g
  map-fibered-map-type-standard-pullback-hom =
    map-equiv equiv-fibered-map-type-standard-pullback-hom

  map-type-standard-pullback-hom-fibered-map :
    fibered-map f g → type-standard-pullback-hom f g
  map-type-standard-pullback-hom-fibered-map =
    map-equiv equiv-type-standard-pullback-hom-fibered-map
```

Below are basic definitions related to the pullback property of the type of
fibered maps.

```agda
  cone-standard-pullback-hom :
    cone (precomp f Y) (postcomp A g) (type-standard-pullback-hom f g)
  cone-standard-pullback-hom =
    cone-standard-pullback (precomp f Y) (postcomp A g)

  cone-pullback-hom :
    cone (precomp f Y) (postcomp A g) (fibered-map f g)
  cone-pullback-hom =
    cone-map
      ( precomp f Y)
      ( postcomp A g)
      ( cone-standard-pullback (precomp f Y) (postcomp A g))
      ( map-type-standard-pullback-hom-fibered-map)

  gap-standard-pullback-hom :
    {l : Level} {C : UU l} →
    cone (precomp f Y) (postcomp A g) C → C → type-standard-pullback-hom f g
  gap-standard-pullback-hom = gap (precomp f Y) (postcomp A g)

  gap-pullback-hom :
    {l : Level} {C : UU l} →
    cone (precomp f Y) (postcomp A g) C → C → fibered-map f g
  gap-pullback-hom c x =
    map-fibered-map-type-standard-pullback-hom (gap-standard-pullback-hom c x)

  is-pullback-fibered-map :
    is-pullback (precomp f Y) (postcomp A g) (cone-pullback-hom)
  is-pullback-fibered-map =
    is-equiv-map-equiv equiv-type-standard-pullback-hom-fibered-map

  universal-property-pullback-fibered-map :
    {l : Level} →
    universal-property-pullback l
      ( precomp f Y) (postcomp A g) (cone-pullback-hom)
  universal-property-pullback-fibered-map =
    universal-property-pullback-is-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom)
      ( is-pullback-fibered-map)
```

### The pullback-hom map

The pullback-hom `f ⋔ g` is the map `(B → X) → fibered-map f g`, that takes a
diagonal map `j` from the codomain of `f` to the domain of `g` to the fibered
map `(g ∘ j , j ∘ f , refl-htpy)`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  pullback-hom : (B → X) → fibered-map f g
  pullback-hom = gap-pullback-hom f g (postcomp B g , precomp f X , refl-htpy)

  infix 30 _⋔_
  _⋔_ = pullback-hom
```

The symbol `⋔` is the [pitchfork](https://codepoints.net/U+22D4) (agda-input:
`\pitchfork`).

## Properties

### The fibers of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : fibered-map f g)
  where

  inv-compute-fiber-pullback-hom :
    fiber (pullback-hom f g) h ≃ lifting-square-fibered-map f g h
  inv-compute-fiber-pullback-hom =
    equiv-tot
      ( λ j →
        ( equiv-Σ _
          ( equiv-inv-htpy (j ∘ f) (map-total-fibered-map f g h))
          ( λ E →
            equiv-Σ _
              ( equiv-inv-htpy (g ∘ j) (map-base-fibered-map f g h))
              ( λ L →
                ( equiv-concat-htpy'
                  ( inv-htpy L ·r f)
                  ( λ x →
                    ap
                      ( is-map-over-map-total-fibered-map f g h x ∙_)
                      ( inv-htpy-left-whisk-inv-htpy g E x))) ∘e
                ( equiv-right-transpose-htpy-concat
                  ( inv-htpy (L ·r f))
                  ( g ·l E)
                  ( is-map-over-map-total-fibered-map f g h)) ∘e
                ( equiv-left-transpose-htpy-concat'
                  ( g ·l E)
                  ( L ·r f)
                  ( is-map-over-map-total-fibered-map f g h))))) ∘e
        ( equiv-left-swap-Σ) ∘e
        ( extensionality-fibered-map f g (pullback-hom f g j) h))

  compute-fiber-pullback-hom :
    lifting-square-fibered-map f g h ≃ fiber (pullback-hom f g) h
  compute-fiber-pullback-hom = inv-equiv inv-compute-fiber-pullback-hom
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
