# Pullback cones

```agda
module foundation.pullback-cones where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.multivariable-homotopies
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
open import foundation-core.universal-property-pullbacks
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

A [cone](foundation.cones-over-cospan-diagrams.md) `𝑐` over a
[cospan diagram](foundation.cospans.md) `A -f-> X <-g- B` with domain `C` is a
{{#concept "pullback cone" Disambiguation="of types" Agda=pullback-cone}} if its
gap map

```text
  C → standard-pullback f g
```

is an [equivalence](foundation-core.equivalences.md). This is known as the
[small predicate of being a pullback](foundation-core.pullbacks.md).

## Definitions

### Pullback cones

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  where

  pullback-cone : (l4 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
  pullback-cone l4 =
    Σ ( Σ ( UU l4)
          ( λ C →
            cone (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) C))
      ( λ (C , c) →
        is-pullback (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) c)

module _
  {l1 l2 l3 l4 : Level} (𝒮 : cospan-diagram l1 l2 l3) (c : pullback-cone 𝒮 l4)
  where

  domain-pullback-cone : UU l4
  domain-pullback-cone = pr1 (pr1 c)

  cone-pullback-cone :
    cone
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( domain-pullback-cone)
  cone-pullback-cone = pr2 (pr1 c)

  vertical-map-pullback-cone :
    domain-pullback-cone → left-type-cospan-diagram 𝒮
  vertical-map-pullback-cone =
    vertical-map-cone
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( cone-pullback-cone)

  horizontal-map-pullback-cone :
    domain-pullback-cone → right-type-cospan-diagram 𝒮
  horizontal-map-pullback-cone =
    horizontal-map-cone
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( cone-pullback-cone)

  coherence-square-pullback-cone :
    coherence-square-maps
      ( horizontal-map-pullback-cone)
      ( vertical-map-pullback-cone)
      ( right-map-cospan-diagram 𝒮)
      ( left-map-cospan-diagram 𝒮)
  coherence-square-pullback-cone =
    coherence-square-cone
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( cone-pullback-cone)

  is-pullback-pullback-cone :
    is-pullback
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( cone-pullback-cone)
  is-pullback-pullback-cone = pr2 c

  up-pullback-cone :
    universal-property-pullback
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( cone-pullback-cone)
  up-pullback-cone =
    universal-property-pullback-is-pullback
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( cone-pullback-cone)
      ( is-pullback-pullback-cone)

  gap-standard-pullback-pullback-cone :
    domain-pullback-cone →
    standard-pullback (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮)
  gap-standard-pullback-pullback-cone =
    gap
      ( left-map-cospan-diagram 𝒮)
      ( right-map-cospan-diagram 𝒮)
      ( cone-pullback-cone)

  map-inv-gap-standard-pullback-pullback-cone :
    standard-pullback (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) →
    domain-pullback-cone
  map-inv-gap-standard-pullback-pullback-cone =
    map-inv-is-equiv is-pullback-pullback-cone

  is-section-map-inv-gap-standard-pullback-pullback-cone :
    is-section
      ( gap-standard-pullback-pullback-cone)
      ( map-inv-gap-standard-pullback-pullback-cone)
  is-section-map-inv-gap-standard-pullback-pullback-cone =
    is-section-map-inv-is-equiv is-pullback-pullback-cone

  is-retraction-map-inv-gap-standard-pullback-pullback-cone :
    is-retraction
      ( gap-standard-pullback-pullback-cone)
      ( map-inv-gap-standard-pullback-pullback-cone)
  is-retraction-map-inv-gap-standard-pullback-pullback-cone =
    is-retraction-map-inv-is-equiv is-pullback-pullback-cone
```

### Horizontal pasting of pullback cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  pasting-horizontal-pullback-cone :
    (c : pullback-cone (Y , C , Z , j , h) l1) →
    pullback-cone
      ( X , domain-pullback-cone (Y , C , Z , j , h) c , Y , i ,
        vertical-map-pullback-cone (Y , C , Z , j , h) c)
      ( l2) →
    pullback-cone (X , C , Z , j ∘ i , h) l2
  pasting-horizontal-pullback-cone ((A , a) , pb-A) ((B , b) , pb-B) =
    ( B , pasting-horizontal-cone i j h a b) ,
    ( is-pullback-rectangle-is-pullback-left-square i j h a b pb-A pb-B)
```

### Vertical pasting of pullback cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  pasting-vertical-pullback-cone :
    (c : pullback-cone (C , Y , Z , f , g) l1) →
    pullback-cone
      ( domain-pullback-cone (C , Y , Z , f , g) c , X , Y ,
        horizontal-map-pullback-cone (C , Y , Z , f , g) c , h) l2 →
    pullback-cone (C , X , Z , f , g ∘ h) l2
  pasting-vertical-pullback-cone ((A , a) , pb-A) ((B , b) , pb-B) =
    ( B , pasting-vertical-cone f g h a b) ,
    ( is-pullback-rectangle-is-pullback-top-square f g h a b pb-A pb-B)
```

### The swapping function on pullback cones

```agda
swap-pullback-cone :
  {l1 l2 l3 l4 : Level} (𝒮 : cospan-diagram l1 l2 l3) →
  pullback-cone 𝒮 l4 →
  pullback-cone (swap-cospan-diagram 𝒮) l4
swap-pullback-cone 𝒮 ((C , c) , pb-C) =
  ( C , swap-cone (left-map-cospan-diagram 𝒮) (right-map-cospan-diagram 𝒮) c) ,
  ( is-pullback-swap-cone
    ( left-map-cospan-diagram 𝒮)
    ( right-map-cospan-diagram 𝒮)
    ( c)
    ( pb-C))
```

### The identity pullback cone over the identity cospan diagram

```agda
id-pullback-cone :
  {l : Level} (A : UU l) → pullback-cone (id-cospan-diagram A) l
id-pullback-cone A = ((A , id-cone A) , is-pullback-id-cone A)
```

### The identity type pullback cone

```agda
module _
  {l : Level} {A : UU l} (x y : A)
  where

  cospan-diagram-Id : cospan-diagram lzero lzero l
  cospan-diagram-Id = (unit , unit , A , point x , point y)

  pullback-cone-Id : pullback-cone cospan-diagram-Id l
  pullback-cone-Id = (((x ＝ y) , cone-Id x y) , is-pullback-Id x y)
```

### The type of equivalences pullback cone

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cospan-diagram-equiv : cospan-diagram (l1 ⊔ l2) lzero (l1 ⊔ l2)
  cospan-diagram-equiv =
    ( (A → B) × (B → A) × (B → A) ,
      unit ,
      (A → A) × (B → B) ,
      (λ (f , g , h) → h ∘ f , f ∘ g) ,
      point (id' A , id' B))

  pullback-cone-equiv : pullback-cone cospan-diagram-equiv (l1 ⊔ l2)
  pullback-cone-equiv = (A ≃ B , cone-equiv) , is-pullback-equiv
```

### The cartesian product pullback cone

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cospan-diagram-cartesian-product : cospan-diagram l1 l2 lzero
  cospan-diagram-cartesian-product =
    ( A , B , unit , terminal-map A , terminal-map B)

  pullback-cone-cartesian-product :
    pullback-cone cospan-diagram-cartesian-product (l1 ⊔ l2)
  pullback-cone-cartesian-product =
    (A × B , cone-cartesian-product A B) , is-pullback-cartesian-product A B
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
