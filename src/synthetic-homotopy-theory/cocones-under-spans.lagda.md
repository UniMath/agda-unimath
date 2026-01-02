# Cocones under spans

```agda
module synthetic-homotopy-theory.cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **cocone under a [span](foundation.spans.md)** `A <-f- S -g-> B` with codomain
`X` consists of two maps `i : A → X` and `j : B → X` equipped with a
[homotopy](foundation.homotopies.md) witnessing that the square

```text
        g
    S -----> B
    |        |
  f |        | j
    ∨        ∨
    A -----> X
        i
```

[commutes](foundation.commuting-squares-of-maps.md).

## Definitions

### Cocones

```agda
cocone :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
cocone {A = A} {B = B} f g X =
  Σ (A → X) (λ i → Σ (B → X) (λ j → coherence-square-maps g f j i))

cocone-span-diagram :
  {l1 l2 l3 l4 : Level} →
  span-diagram l1 l2 l3 → UU l4 →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
cocone-span-diagram 𝒮 X =
  cocone (left-map-span-diagram 𝒮) (right-map-span-diagram 𝒮) X

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g X)
  where

  horizontal-map-cocone : A → X
  horizontal-map-cocone = pr1 c

  vertical-map-cocone : B → X
  vertical-map-cocone = pr1 (pr2 c)

  coherence-square-cocone :
    coherence-square-maps g f vertical-map-cocone horizontal-map-cocone
  coherence-square-cocone = pr2 (pr2 c)
```

### Homotopies of cocones

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4}
  where

  statement-coherence-htpy-cocone :
    (c c' : cocone f g X) →
    (K : horizontal-map-cocone f g c ~ horizontal-map-cocone f g c')
    (L : vertical-map-cocone f g c ~ vertical-map-cocone f g c') →
    UU (l1 ⊔ l4)
  statement-coherence-htpy-cocone c c' K L =
    (coherence-square-cocone f g c ∙h (L ·r g)) ~
    ((K ·r f) ∙h coherence-square-cocone f g c')

  htpy-cocone : (c c' : cocone f g X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-cocone c c' =
    Σ ( horizontal-map-cocone f g c ~ horizontal-map-cocone f g c')
      ( λ K →
        Σ ( vertical-map-cocone f g c ~ vertical-map-cocone f g c')
          ( statement-coherence-htpy-cocone c c' K))

  module _
    (c c' : cocone f g X) (H : htpy-cocone c c')
    where

    horizontal-htpy-cocone :
      horizontal-map-cocone f g c ~ horizontal-map-cocone f g c'
    horizontal-htpy-cocone = pr1 H

    vertical-htpy-cocone :
      vertical-map-cocone f g c ~ vertical-map-cocone f g c'
    vertical-htpy-cocone = pr1 (pr2 H)

    coherence-htpy-cocone :
      statement-coherence-htpy-cocone c c'
        ( horizontal-htpy-cocone)
        ( vertical-htpy-cocone)
    coherence-htpy-cocone = pr2 (pr2 H)

  refl-htpy-cocone :
    (c : cocone f g X) → htpy-cocone c c
  pr1 (refl-htpy-cocone (i , j , H)) = refl-htpy
  pr1 (pr2 (refl-htpy-cocone (i , j , H))) = refl-htpy
  pr2 (pr2 (refl-htpy-cocone (i , j , H))) = right-unit-htpy

  htpy-eq-cocone :
    (c c' : cocone f g X) → c ＝ c' → htpy-cocone c c'
  htpy-eq-cocone c .c refl = refl-htpy-cocone c

  module _
    (c c' : cocone f g X)
    (p : c ＝ c')
    where

    horizontal-htpy-eq-cocone :
      horizontal-map-cocone f g c ~
      horizontal-map-cocone f g c'
    horizontal-htpy-eq-cocone =
      horizontal-htpy-cocone c c' (htpy-eq-cocone c c' p)

    vertical-htpy-eq-cocone :
      vertical-map-cocone f g c ~
      vertical-map-cocone f g c'
    vertical-htpy-eq-cocone =
      vertical-htpy-cocone c c' (htpy-eq-cocone c c' p)

    coherence-square-htpy-eq-cocone :
      statement-coherence-htpy-cocone c c'
        ( horizontal-htpy-eq-cocone)
        ( vertical-htpy-eq-cocone)
    coherence-square-htpy-eq-cocone =
      coherence-htpy-cocone c c' (htpy-eq-cocone c c' p)

  is-torsorial-htpy-cocone :
    (c : cocone f g X) → is-torsorial (htpy-cocone c)
  is-torsorial-htpy-cocone c =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (horizontal-map-cocone f g c))
      ( horizontal-map-cocone f g c , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (vertical-map-cocone f g c))
        ( vertical-map-cocone f g c , refl-htpy)
        ( is-contr-is-equiv'
          ( Σ ( horizontal-map-cocone f g c ∘ f ~ vertical-map-cocone f g c ∘ g)
              ( λ H' → coherence-square-cocone f g c ~ H'))
          ( tot (λ H' M → right-unit-htpy ∙h M))
          ( is-equiv-tot-is-fiberwise-equiv (λ H' → is-equiv-concat-htpy _ _))
          ( is-torsorial-htpy (coherence-square-cocone f g c))))

  is-equiv-htpy-eq-cocone :
    (c c' : cocone f g X) → is-equiv (htpy-eq-cocone c c')
  is-equiv-htpy-eq-cocone c =
    fundamental-theorem-id
      ( is-torsorial-htpy-cocone c)
      ( htpy-eq-cocone c)

  extensionality-cocone :
    (c c' : cocone f g X) → (c ＝ c') ≃ htpy-cocone c c'
  pr1 (extensionality-cocone c c') = htpy-eq-cocone c c'
  pr2 (extensionality-cocone c c') = is-equiv-htpy-eq-cocone c c'

  eq-htpy-cocone :
    (c c' : cocone f g X) → htpy-cocone c c' → c ＝ c'
  eq-htpy-cocone c c' = map-inv-is-equiv (is-equiv-htpy-eq-cocone c c')
```

### Postcomposing cocones under spans with maps

```agda
cocone-map :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} {Y : UU l5} →
  cocone f g X → (X → Y) → cocone f g Y
pr1 (cocone-map f g c h) = h ∘ horizontal-map-cocone f g c
pr1 (pr2 (cocone-map f g c h)) = h ∘ vertical-map-cocone f g c
pr2 (pr2 (cocone-map f g c h)) = h ·l coherence-square-cocone f g c

cocone-map-span-diagram :
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} (c : cocone-span-diagram 𝒮 X) →
  {l5 : Level} {Y : UU l5} →
  (X → Y) → cocone-span-diagram 𝒮 Y
cocone-map-span-diagram {𝒮 = 𝒮} c =
  cocone-map (left-map-span-diagram 𝒮) (right-map-span-diagram 𝒮) c

cocone-map-id :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  cocone-map f g c id ＝ c
cocone-map-id f g c =
  eq-pair-eq-fiber
    ( eq-pair-eq-fiber (eq-htpy (ap-id ∘ coherence-square-cocone f g c)))

cocone-map-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  {Y : UU l5} (h : X → Y) {Z : UU l6} (k : Y → Z) →
  cocone-map f g c (k ∘ h) ＝ cocone-map f g (cocone-map f g c h) k
cocone-map-comp f g (i , j , H) h k =
  eq-pair-eq-fiber (eq-pair-eq-fiber (eq-htpy (ap-comp k h ∘ H)))
```

### Horizontal composition of cocones

```text
        i       k
    A ----> B ----> C
    |       |       |
  f |       |       |
    ∨       ∨       ∨
    X ----> Y ----> Z
```

```agda
cocone-comp-horizontal :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → X) (i : A → B) (k : B → C) ( c : cocone f i Y) →
  cocone (vertical-map-cocone f i c) k Z → cocone f (k ∘ i) Z
pr1 (cocone-comp-horizontal f i k c d) =
  ( horizontal-map-cocone (vertical-map-cocone f i c) k d) ∘
  ( horizontal-map-cocone f i c)
pr1 (pr2 (cocone-comp-horizontal f i k c d)) =
  vertical-map-cocone (vertical-map-cocone f i c) k d
pr2 (pr2 (cocone-comp-horizontal f i k c d)) =
  pasting-horizontal-coherence-square-maps
    ( i)
    ( k)
    ( f)
    ( vertical-map-cocone f i c)
    ( vertical-map-cocone (vertical-map-cocone f i c) k d)
    ( horizontal-map-cocone f i c)
    ( horizontal-map-cocone (vertical-map-cocone f i c) k d)
    ( coherence-square-cocone f i c)
    ( coherence-square-cocone (vertical-map-cocone f i c) k d)
```

A variation on the above:

```text
        i       k
    A ----> B ----> C
    |       |       |
  f |     g |       |
    ∨       ∨       ∨
    X ----> Y ----> Z
        j
```

```agda
cocone-comp-horizontal' :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → X) (i : A → B) (k : B → C) (g : B → Y) (j : X → Y) →
  cocone g k Z → coherence-square-maps i f g j →
  cocone f (k ∘ i) Z
cocone-comp-horizontal' f i k g j c coh =
  cocone-comp-horizontal f i k (j , g , coh) c
```

### Vertical composition of cocones

```text
        i
    A -----> X
    |        |
  f |        |
    ∨        ∨
    B -----> Y
    |        |
  k |        |
    ∨        ∨
    C -----> Z
```

```agda
cocone-comp-vertical :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → B) (i : A → X) (k : B → C) (c : cocone f i Y) →
  cocone k (horizontal-map-cocone f i c) Z → cocone (k ∘ f) i Z
pr1 (cocone-comp-vertical f i k c d) =
  horizontal-map-cocone k (horizontal-map-cocone f i c) d
pr1 (pr2 (cocone-comp-vertical f i k c d)) =
  vertical-map-cocone k (horizontal-map-cocone f i c) d ∘
  vertical-map-cocone f i c
pr2 (pr2 (cocone-comp-vertical f i k c d)) =
  pasting-vertical-coherence-square-maps
    ( i)
    ( f)
    ( vertical-map-cocone f i c)
    ( horizontal-map-cocone f i c)
    ( k)
    ( vertical-map-cocone k (horizontal-map-cocone f i c) d)
    ( horizontal-map-cocone k (horizontal-map-cocone f i c) d)
    ( coherence-square-cocone f i c)
    ( coherence-square-cocone k (horizontal-map-cocone f i c) d)
```

A variation on the above:

```text
        i
    A -----> X
    |        |
  f |        | g
    ∨   j    ∨
    B -----> Y
    |        |
  k |        |
    ∨        ∨
    C -----> Z
```

```agda
cocone-comp-vertical' :
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → B) (i : A → X) (g : X → Y) (j : B → Y) (k : B → C) →
  cocone k j Z → coherence-square-maps i f g j →
  cocone (k ∘ f) i Z
cocone-comp-vertical' f i g j k c coh =
  cocone-comp-vertical f i k (j , g , coh) c
```

Given a commutative diagram like this,

```text
           g'
       S' ---> B'
      / \       \
  f' /   \ k     \ j
    /     ∨   g   ∨
   A'     S ----> B
     \    |       |
    i \   | f     |
       \  ∨       ∨
        > A ----> X
```

we can compose both vertically and horizontally to get the following cocone:

```text
  S' ---> B'
  |       |
  |       |
  ∨       ∨
  A' ---> X
```

Notice that the triple `(i,j,k)` is really a morphism of spans. So the resulting
cocone arises as a composition of the original cocone with this morphism of
spans.

```agda
comp-cocone-hom-span :
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { S' : UU l5} {A' : UU l6} {B' : UU l7}
  ( f : S → A) (g : S → B) (f' : S' → A') (g' : S' → B')
  ( i : A' → A) (j : B' → B) (k : S' → S) →
  cocone f g X →
  coherence-square-maps k f' f i → coherence-square-maps g' k j g →
  cocone f' g' X
comp-cocone-hom-span f g f' g' i j k c coh-l coh-r =
  cocone-comp-vertical
    ( id)
    ( g')
    ( f')
    ( (g ∘ k , j , coh-r))
    ( cocone-comp-horizontal f' k g (i , f , coh-l) c)
```

### The diagonal cocone on a span of identical maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (X : UU l3)
  where

  diagonal-into-cocone :
    (B → X) → cocone f f X
  pr1 (diagonal-into-cocone g) = g
  pr1 (pr2 (diagonal-into-cocone g)) = g
  pr2 (pr2 (diagonal-into-cocone g)) = refl-htpy
```

### Cocones obtained from morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  cocone-hom-arrow : cocone f (map-domain-hom-arrow f g h) Y
  pr1 cocone-hom-arrow = map-codomain-hom-arrow f g h
  pr1 (pr2 cocone-hom-arrow) = g
  pr2 (pr2 cocone-hom-arrow) = coh-hom-arrow f g h
```

### The swapping function on cocones over spans

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4)
  where

  swap-cocone : cocone f g X → cocone g f X
  pr1 (swap-cocone c) = vertical-map-cocone f g c
  pr1 (pr2 (swap-cocone c)) = horizontal-map-cocone f g c
  pr2 (pr2 (swap-cocone c)) = inv-htpy (coherence-square-cocone f g c)

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4)
  where

  is-involution-swap-cocone : swap-cocone g f X ∘ swap-cocone f g X ~ id
  is-involution-swap-cocone c =
    eq-htpy-cocone f g
      ( swap-cocone g f X (swap-cocone f g X c))
      ( c)
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ s →
          concat
            ( right-unit)
            ( coherence-square-cocone f g c s)
            ( inv-inv (coherence-square-cocone f g c s))))

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4)
  where

  is-equiv-swap-cocone : is-equiv (swap-cocone f g X)
  is-equiv-swap-cocone =
    is-equiv-is-invertible
      ( swap-cocone g f X)
      ( is-involution-swap-cocone g f X)
      ( is-involution-swap-cocone f g X)

  equiv-swap-cocone : cocone f g X ≃ cocone g f X
  pr1 equiv-swap-cocone = swap-cocone f g X
  pr2 equiv-swap-cocone = is-equiv-swap-cocone
```
