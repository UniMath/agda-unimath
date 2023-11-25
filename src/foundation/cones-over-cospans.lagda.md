# Cones over cospans

```agda
module foundation.cones-over-cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **cone over a [cospan](foundation.cospans.md)** `A -f-> X <-g- B` with domain
`C` is a triple `(p, q, H)` consisting of a map `p : C → A`, a map `q : C → B`,
and a homotopy `H` witnessing that the square

```text
      q
  C -----> B
  |        |
 p|        |g
  V        V
  A -----> X
      f
```

commutes.

## Definitions

### Cones over cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  cone : {l4 : Level} → UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cone C = Σ (C → A) (λ p → Σ (C → B) (λ q → coherence-square-maps q p g f))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  vertical-map-cone : C → A
  vertical-map-cone = pr1 c

  horizontal-map-cone : C → B
  horizontal-map-cone = pr1 (pr2 c)

  coherence-square-cone :
    coherence-square-maps horizontal-map-cone vertical-map-cone g f
  coherence-square-cone = pr2 (pr2 c)

  hom-arrow-cone : hom-arrow vertical-map-cone g
  pr1 hom-arrow-cone = horizontal-map-cone
  pr1 (pr2 hom-arrow-cone) = f
  pr2 (pr2 hom-arrow-cone) = coherence-square-cone

  hom-arrow-cone' : hom-arrow horizontal-map-cone f
  hom-arrow-cone' = transpose-hom-arrow vertical-map-cone g hom-arrow-cone
```

### Dependent cones over cospans

```agda
cone-family :
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7}
  {f : A → X} {g : B → X} →
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b)) →
  cone f g C → (C → UU l8) → UU (l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
cone-family {C = C} PX {f = f} {g} f' g' c PC =
  (x : C) →
  cone
    ( ( tr PX (coherence-square-cone f g c x)) ∘
      ( f' (vertical-map-cone f g c x)))
    ( g' (horizontal-map-cone f g c x))
    ( PC x)
```

### Identifications of cones over cospans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where

  coherence-htpy-cone :
    (c c' : cone f g C)
    (K : vertical-map-cone f g c ~ vertical-map-cone f g c')
    (L : horizontal-map-cone f g c ~ horizontal-map-cone f g c') → UU (l4 ⊔ l3)
  coherence-htpy-cone c c' K L =
    ( coherence-square-cone f g c ∙h (g ·l L)) ~
    ( (f ·l K) ∙h coherence-square-cone f g c')

  htpy-cone : cone f g C → cone f g C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-cone c c' =
    Σ ( vertical-map-cone f g c ~ vertical-map-cone f g c')
      ( λ K →
        Σ ( horizontal-map-cone f g c ~ horizontal-map-cone f g c')
          ( coherence-htpy-cone c c' K))

  refl-htpy-cone : (c : cone f g C) → htpy-cone c c
  pr1 (refl-htpy-cone c) = refl-htpy
  pr1 (pr2 (refl-htpy-cone c)) = refl-htpy
  pr2 (pr2 (refl-htpy-cone c)) = right-unit-htpy

  htpy-eq-cone : (c c' : cone f g C) → c ＝ c' → htpy-cone c c'
  htpy-eq-cone c .c refl = refl-htpy-cone c

  is-torsorial-htpy-cone :
    (c : cone f g C) → is-torsorial (htpy-cone c)
  is-torsorial-htpy-cone c =
    is-torsorial-Eq-structure
      ( λ p qH K →
        Σ ( horizontal-map-cone f g c ~ pr1 qH)
          ( coherence-htpy-cone c (p , qH) K))
      ( is-torsorial-htpy (vertical-map-cone f g c))
      ( vertical-map-cone f g c , refl-htpy)
      ( is-torsorial-Eq-structure
        ( λ q H →
          coherence-htpy-cone c
            ( vertical-map-cone f g c , q , H)
            ( refl-htpy))
        ( is-torsorial-htpy (horizontal-map-cone f g c))
        ( horizontal-map-cone f g c , refl-htpy)
        ( is-torsorial-htpy (coherence-square-cone f g c ∙h refl-htpy)))

  is-equiv-htpy-eq-cone : (c c' : cone f g C) → is-equiv (htpy-eq-cone c c')
  is-equiv-htpy-eq-cone c =
    fundamental-theorem-id (is-torsorial-htpy-cone c) (htpy-eq-cone c)

  extensionality-cone : (c c' : cone f g C) → (c ＝ c') ≃ htpy-cone c c'
  pr1 (extensionality-cone c c') = htpy-eq-cone c c'
  pr2 (extensionality-cone c c') = is-equiv-htpy-eq-cone c c'

  eq-htpy-cone : (c c' : cone f g C) → htpy-cone c c' → c ＝ c'
  eq-htpy-cone c c' = map-inv-equiv (extensionality-cone c c')
```

### Precomposing cones over cospans with a map

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  cone-map :
    {C : UU l4} → cone f g C → {C' : UU l5} → (C' → C) → cone f g C'
  pr1 (cone-map c h) = vertical-map-cone f g c ∘ h
  pr1 (pr2 (cone-map c h)) = horizontal-map-cone f g c ∘ h
  pr2 (pr2 (cone-map c h)) = coherence-square-cone f g c ·r h
```

### Pasting cones horizontally

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  pasting-horizontal-cone :
    (c : cone j h B) → cone i (vertical-map-cone j h c) A → cone (j ∘ i) h A
  pr1 (pasting-horizontal-cone c (f , p , H)) = f
  pr1 (pr2 (pasting-horizontal-cone c (f , p , H))) =
    (horizontal-map-cone j h c) ∘ p
  pr2 (pr2 (pasting-horizontal-cone c (f , p , H))) =
    pasting-horizontal-coherence-square-maps p
      ( horizontal-map-cone j h c)
      ( f)
      ( vertical-map-cone j h c)
      ( h)
      ( i)
      ( j)
      ( H)
      ( coherence-square-cone j h c)
```

### Vertical composition of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  pasting-vertical-cone :
    (c : cone f g B) → cone (horizontal-map-cone f g c) h A → cone f (g ∘ h) A
  pr1 (pasting-vertical-cone c (p' , q' , H')) =
    ( vertical-map-cone f g c) ∘ p'
  pr1 (pr2 (pasting-vertical-cone c (p' , q' , H'))) = q'
  pr2 (pr2 (pasting-vertical-cone c (p' , q' , H'))) =
    pasting-vertical-coherence-square-maps q' p' h
      ( horizontal-map-cone f g c)
      ( vertical-map-cone f g c)
      ( g)
      ( f)
      ( H')
      ( coherence-square-cone f g c)
```

### The swapping function on cones over cospans

```agda
swap-cone :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → cone g f C
pr1 (swap-cone f g c) = horizontal-map-cone f g c
pr1 (pr2 (swap-cone f g c)) = vertical-map-cone f g c
pr2 (pr2 (swap-cone f g c)) = inv-htpy (coherence-square-cone f g c)
```

### Parallel cones over cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  coherence-htpy-parallel-cone :
    {l4 : Level} {C : UU l4} (c : cone f g C) (c' : cone f' g' C)
    (Hp : vertical-map-cone f g c ~ vertical-map-cone f' g' c')
    (Hq : horizontal-map-cone f g c ~ horizontal-map-cone f' g' c') →
    UU (l3 ⊔ l4)
  coherence-htpy-parallel-cone c c' Hp Hq =
    ( ( coherence-square-cone f g c) ∙h
      ( (g ·l Hq) ∙h (Hg ·r horizontal-map-cone f' g' c'))) ~
    ( ( (f ·l Hp) ∙h (Hf ·r (vertical-map-cone f' g' c'))) ∙h
      ( coherence-square-cone f' g' c'))

  fam-htpy-parallel-cone :
    {l4 : Level} {C : UU l4} (c : cone f g C) → (c' : cone f' g' C) →
    (vertical-map-cone f g c ~ vertical-map-cone f' g' c') → UU (l2 ⊔ l3 ⊔ l4)
  fam-htpy-parallel-cone c c' Hp =
    Σ ( horizontal-map-cone f g c ~ horizontal-map-cone f' g' c')
      ( coherence-htpy-parallel-cone c c' Hp)

  htpy-parallel-cone :
    {l4 : Level} {C : UU l4} →
    cone f g C → cone f' g' C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-parallel-cone c c' =
    Σ ( vertical-map-cone f g c ~ vertical-map-cone f' g' c')
      ( fam-htpy-parallel-cone c c')
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
