# The pullback-hom

```agda
module orthogonal-factorization-systems.pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibered-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.morphisms-cospans
open import foundation.pullbacks
open import foundation.universe-levels
```

</details>

## Idea

Given a pair of maps `f : A → B` and `g : X → Y`, there is a commuting square

```text
          - ∘ f
    B → X ----> A → X
      |           |
g ∘ - |           | g ∘ -
      V           V
    B → Y ----> A → Y.
          - ∘ f
```

The **pullback-hom** of `f` and `g` is the comparison map from `B → X` to the
[pullback](foundation.pullbacks.md) of the [cospan](foundation.cospans.md):

```text
      ∙ ------> A → X
      |  ⌟        |
      |           | g ∘ -
      V           V
    B → Y ----> A → Y.
          - ∘ f
```

This pullback type can be canonically understood as the type of
[fibered maps](foundation.fibered-maps.md) from `f` to `g`, i.e. commuting
squares where the vertical maps are `f` and `g`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  type-pullback-hom : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-pullback-hom = canonical-pullback (precomp f Y) (postcomp A g)

  cone-pullback-hom : cone (precomp f Y) (postcomp A g) (type-pullback-hom)
  cone-pullback-hom = cone-canonical-pullback (precomp f Y) (postcomp A g)

  gap-pullback-hom :
    {l : Level} {C : UU l} →
    cone (precomp f Y) (postcomp A g) C → C → type-pullback-hom
  gap-pullback-hom = gap (precomp f Y) (postcomp A g)
```

### The pullback-hom map

The pullback-hom is the canonical gap map `(B → X) → type-pullback-hom` and can
be interpreted as the map that takes a diagonal map `j` from the codomain of `f`
to the domain of `g` to the fibered map `((g ∘ j) , (j ∘ f) , refl-htpy)`.

```agda
  pullback-hom : (B → X) → type-pullback-hom
  pullback-hom =
    gap-pullback-hom (postcomp B g , precomp f X , refl-htpy)
```

## Properties

### Functoriality of the pullback-hom construction

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {l1' l2' l3' l4' : Level}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  where

  map-pullback-hom :
      hom-cospan (precomp f' Y') (postcomp A' g') (precomp f Y) (postcomp A g) →
      type-pullback-hom f' g' → type-pullback-hom f g
  map-pullback-hom =
    map-canonical-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( precomp f' Y')
      ( postcomp A' g')
```

### The pullback-hom type is equivalent to the type of fibered maps between `f` and `g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  equiv-fibered-map-type-pullback-hom :
    type-pullback-hom f g ≃ fibered-map f g
  equiv-fibered-map-type-pullback-hom =
    equiv-tot (λ i → equiv-tot (λ h → equiv-funext))
```
