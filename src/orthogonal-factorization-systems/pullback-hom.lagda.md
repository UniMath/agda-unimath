---
title: Pullback-hom
---

```agda
module orthogonal-factorization-systems.pullback-hom where

open import foundation.cones-pullbacks
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.homotopies
open import foundation.morphisms-cospans
open import foundation.pullbacks
open import foundation.universe-levels
```

## Idea

Given a pair of maps `f : A → X` and `g : B → Y`, there is a
commuting square

```md
          - ∘ f  
    B → X ----> B → A
      |            |
g ∘ - |            | g ∘ -
      V            V
    Y → X ----> Y → A.
          - ∘ f  
```

The _pullback-hom_ of `f` and `g` is the pullback of the cospan:

```md
      P -------> B → A
      |  ⌟         |
      |            | g ∘ -
      V            V
    Y → X ----> Y → A.
          - ∘ f
```

The pullback-hom of `f` and `g` can be canonically understood as the
type of fibered maps from `f` to `g`. I.e. commuting squares where the
vertical maps are `f` and `g`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  pullback-hom : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pullback-hom = canonical-pullback (precomp f Y) (postcomp A g)
  
  cone-pullback-hom : cone (precomp f Y) (postcomp A g) (pullback-hom)
  cone-pullback-hom = cone-canonical-pullback (precomp f Y) (postcomp A g)

  gap-pullback-hom :
    {l : Level} {C : UU l} → cone (precomp f Y) (postcomp A g) C → C → pullback-hom
  gap-pullback-hom = gap (precomp f Y) (postcomp A g)
```

### The diagonal pullback-hom map

The pullback-hom type comes equipped with a canonical comparison map
`(X → B) → pullback-hom` which we can interpret as the map that takes
a diagonal map `j` from the codomain of `f` to the domain of `g` to
the fibered map `((g ∘ j) , (j ∘ f) , refl-htpy)`.

```agda
  diagonal-pullback-hom : (X → B) → pullback-hom
  diagonal-pullback-hom = gap-pullback-hom (postcomp X g , precomp f B , refl-htpy)
```

## Properties

### Functoriality of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  {l1' l2' l3' l4' : Level} {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → X') (g' : B' → Y')
  where

  map-pullback-hom :
      hom-cospan (precomp f' Y') (postcomp A' g') (precomp f Y) (postcomp A g) →
      pullback-hom f' g' → pullback-hom f g
  map-pullback-hom =
    map-canonical-pullback (precomp f Y) (postcomp A g) (precomp f' Y') (postcomp A' g')
```
