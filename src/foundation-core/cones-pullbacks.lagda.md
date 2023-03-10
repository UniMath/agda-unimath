# Cones on pullback diagrams

```agda
module foundation-core.cones-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies
open import foundation.structure-identity-principle

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.universe-levels
```

</details>

## Idea

A cone on a cospan `A --f--> X <--g-- B` with vertex `C` is a triple `(p,q,H)` consisting of a map `p : C → A`, a map `q : C → B`, and a homotopy `H` witnessing that the square

```md
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

### Cones on cospans

A cone on a cospan with a vertex C is a pair of functions from C into the domains of the maps in the cospan, equipped with a homotopy witnessing that the resulting square commutes.

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
```

### Dependent cones

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

### Identifications of cones

Next we characterize the identity type of the type of cones with a given vertex C. Note that in the definition of htpy-cone we do not use pattern matching on the cones c and c'. This is to ensure that the type htpy-cone f g c c' is a Σ-type for any c and c', not just for c and c' of the form (pair p (pair q H)) and (pair p' (pair q' H')) respectively.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where

  coherence-htpy-cone :
    (c c' : cone f g C) (K : vertical-map-cone f g c ~ vertical-map-cone f g c')
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

  is-contr-total-htpy-cone :
    (c : cone f g C) → is-contr (Σ (cone f g C) (htpy-cone c))
  is-contr-total-htpy-cone c =
    is-contr-total-Eq-structure
      ( λ p qH K →
        Σ ( horizontal-map-cone f g c ~ pr1 qH)
          ( coherence-htpy-cone c (pair p qH) K))
      ( is-contr-total-htpy (vertical-map-cone f g c))
      ( pair (vertical-map-cone f g c) refl-htpy)
      ( is-contr-total-Eq-structure
        ( λ q H →
          coherence-htpy-cone c
            ( pair (vertical-map-cone f g c) (pair q H))
            ( refl-htpy))
        ( is-contr-total-htpy (horizontal-map-cone f g c))
        ( pair (horizontal-map-cone f g c) refl-htpy)
        ( is-contr-total-htpy (coherence-square-cone f g c ∙h refl-htpy)))

  is-equiv-htpy-eq-cone : (c c' : cone f g C) → is-equiv (htpy-eq-cone c c')
  is-equiv-htpy-eq-cone c =
    fundamental-theorem-id (is-contr-total-htpy-cone c) (htpy-eq-cone c)

  extensionality-cone : (c c' : cone f g C) → (c ＝ c') ≃ htpy-cone c c'
  pr1 (extensionality-cone c c') = htpy-eq-cone c c'
  pr2 (extensionality-cone c c') = is-equiv-htpy-eq-cone c c'

  eq-htpy-cone : (c c' : cone f g C) → htpy-cone c c' → (c ＝ c')
  eq-htpy-cone c c' = map-inv-equiv (extensionality-cone c c')
```

### Precomposing cones

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  cone-map :
    {l4 l5 : Level} {C : UU l4} {C' : UU l5} →
    cone f g C → (C' → C) → cone f g C'
  pr1 (cone-map c h) = vertical-map-cone f g c ∘ h
  pr1 (pr2 (cone-map c h)) = horizontal-map-cone f g c ∘ h
  pr2 (pr2 (cone-map c h)) = coherence-square-cone f g c ·r h
```

### Horizontal composition of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  cone-comp-horizontal :
    (c : cone j h B) → cone i (vertical-map-cone j h c) A → cone (j ∘ i) h A
  pr1 (cone-comp-horizontal c (pair f (pair p H))) = f
  pr1 (pr2 (cone-comp-horizontal c (pair f (pair p H)))) =
    (horizontal-map-cone j h c) ∘ p
  pr2 (pr2 (cone-comp-horizontal c (pair f (pair p H)))) =
    coherence-square-maps-comp-horizontal p
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

  cone-comp-vertical :
    (c : cone f g B) → cone (horizontal-map-cone f g c) h A → cone f (g ∘ h) A
  pr1 (cone-comp-vertical c (pair p' (pair q' H'))) =
    ( vertical-map-cone f g c) ∘ p'
  pr1 (pr2 (cone-comp-vertical c (pair p' (pair q' H')))) = q'
  pr2 (pr2 (cone-comp-vertical c (pair p' (pair q' H')))) =
    coherence-square-maps-comp-vertical q' p' h
      ( horizontal-map-cone f g c)
      ( vertical-map-cone f g c)
      ( g)
      ( f)
      ( H')
      ( coherence-square-cone f g c)
```

### The swapping function on cones

```agda
swap-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → cone g f C
pr1 (swap-cone f g c) = horizontal-map-cone f g c
pr1 (pr2 (swap-cone f g c)) = vertical-map-cone f g c
pr2 (pr2 (swap-cone f g c)) = inv-htpy (coherence-square-cone f g c)
```

### Parallel cones

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  coherence-htpy-parallel-cone :
    {l4 : Level} {C : UU l4} (c : cone f g C) (c' : cone f' g' C)
    (Hp : vertical-map-cone f g c ~ vertical-map-cone f' g' c')
    (Hq : horizontal-map-cone f g c ~ horizontal-map-cone f' g' c') → UU _
  coherence-htpy-parallel-cone c c' Hp Hq =
    ( ( coherence-square-cone f g c) ∙h
      ( (g ·l Hq) ∙h (Hg ·r horizontal-map-cone f' g' c'))) ~
    ( ( (f ·l Hp) ∙h (Hf ·r (vertical-map-cone f' g' c'))) ∙h
      ( coherence-square-cone f' g' c'))

  fam-htpy-parallel-cone :
    {l4 : Level} {C : UU l4}  (c : cone f g C) → (c' : cone f' g' C) →
    (vertical-map-cone f g c ~ vertical-map-cone f' g' c') → UU _
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
