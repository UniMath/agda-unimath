# Maps fibered over a map

```agda
module foundation.fibered-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-truncated-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-slice
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.small-types
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

Consider a diagram of the form

```text
    A         B
    |         |
  f |         | g
    ∨         ∨
    X ------> Y
         i
```

A **fibered map** from `f` to `g` over `i` is a map `h : A → B` such that the
square `i ∘ f ~ g ∘ h` [commutes](foundation-core.commuting-squares-of-maps.md).

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-map-over : (X → Y) → (A → B) → UU (l1 ⊔ l4)
  is-map-over i h = coherence-square-maps h f g i

  map-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l4)
  map-over i = Σ (A → B) (is-map-over i)

  fibered-map : UU (l1 ⊔ l3 ⊔ l2 ⊔ l4)
  fibered-map = Σ (X → Y) (map-over)

  fiberwise-map-over : (X → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiberwise-map-over i = (x : X) → fiber f x → fiber g (i x)

  cone-fibered-map : (ihH : fibered-map) → cone (pr1 ihH) g A
  pr1 (cone-fibered-map ihH) = f
  pr1 (pr2 (cone-fibered-map (i , h , H))) = h
  pr2 (pr2 (cone-fibered-map (i , h , H))) = H

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  map-total-map-over : (i : X → Y) → map-over f g i → A → B
  map-total-map-over i = pr1

  is-map-over-map-total-map-over :
    (i : X → Y) (m : map-over f g i) →
    is-map-over f g i (map-total-map-over i m)
  is-map-over-map-total-map-over i = pr2

  map-over-fibered-map : (m : fibered-map f g) → map-over f g (pr1 m)
  map-over-fibered-map = pr2

  map-base-fibered-map : (m : fibered-map f g) → X → Y
  map-base-fibered-map = pr1

  map-total-fibered-map : (m : fibered-map f g) → A → B
  map-total-fibered-map = pr1 ∘ pr2

  is-map-over-map-total-fibered-map :
    (m : fibered-map f g) →
    is-map-over f g (map-base-fibered-map m) (map-total-fibered-map m)
  is-map-over-map-total-fibered-map = pr2 ∘ pr2
```

## Properties

### Identifications of maps over

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  coherence-htpy-map-over :
    (m m' : map-over f g i) →
    map-total-map-over f g i m ~ map-total-map-over f g i m' → UU (l1 ⊔ l4)
  coherence-htpy-map-over m m' K =
    ( is-map-over-map-total-map-over f g i m ∙h (g ·l K)) ~
    ( is-map-over-map-total-map-over f g i m')

  htpy-map-over : (m m' : map-over f g i) → UU (l1 ⊔ l2 ⊔ l4)
  htpy-map-over m m' =
    Σ ( map-total-map-over f g i m ~ map-total-map-over f g i m')
      ( coherence-htpy-map-over m m')

  refl-htpy-map-over : (m : map-over f g i) → htpy-map-over m m
  pr1 (refl-htpy-map-over m) = refl-htpy
  pr2 (refl-htpy-map-over m) = right-unit-htpy

  htpy-eq-map-over : (m m' : map-over f g i) → m ＝ m' → htpy-map-over m m'
  htpy-eq-map-over m .m refl = refl-htpy-map-over m

  is-torsorial-htpy-map-over :
    (m : map-over f g i) → is-torsorial (htpy-map-over m)
  is-torsorial-htpy-map-over m =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-total-map-over f g i m))
      ( map-total-map-over f g i m , refl-htpy)
      ( is-torsorial-htpy (is-map-over-map-total-map-over f g i m ∙h refl-htpy))

  is-equiv-htpy-eq-map-over :
    (m m' : map-over f g i) → is-equiv (htpy-eq-map-over m m')
  is-equiv-htpy-eq-map-over m =
    fundamental-theorem-id (is-torsorial-htpy-map-over m) (htpy-eq-map-over m)

  extensionality-map-over :
    (m m' : map-over f g i) → (m ＝ m') ≃ (htpy-map-over m m')
  pr1 (extensionality-map-over m m') = htpy-eq-map-over m m'
  pr2 (extensionality-map-over m m') = is-equiv-htpy-eq-map-over m m'

  eq-htpy-map-over : (m m' : map-over f g i) → htpy-map-over m m' → m ＝ m'
  eq-htpy-map-over m m' = map-inv-equiv (extensionality-map-over m m')
```

### Identifications of fibered maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  coherence-htpy-fibered-map :
    (m m' : fibered-map f g) →
    map-base-fibered-map f g m ~ map-base-fibered-map f g m' →
    map-total-fibered-map f g m ~ map-total-fibered-map f g m' → UU (l1 ⊔ l4)
  coherence-htpy-fibered-map m m' I H =
    ( is-map-over-map-total-fibered-map f g m ∙h (g ·l H)) ~
    ( (I ·r f) ∙h is-map-over-map-total-fibered-map f g m')

  htpy-fibered-map : (m m' : fibered-map f g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-fibered-map m m' =
    Σ ( map-base-fibered-map f g m ~ map-base-fibered-map f g m')
      ( λ I →
      Σ ( map-total-fibered-map f g m ~ map-total-fibered-map f g m')
        ( coherence-htpy-fibered-map m m' I))

  refl-htpy-fibered-map : (m : fibered-map f g) → htpy-fibered-map m m
  pr1 (refl-htpy-fibered-map m) = refl-htpy
  pr1 (pr2 (refl-htpy-fibered-map m)) = refl-htpy
  pr2 (pr2 (refl-htpy-fibered-map m)) =
    inv-htpy-left-unit-htpy ∙h right-unit-htpy

  htpy-eq-fibered-map :
    (m m' : fibered-map f g) → m ＝ m' → htpy-fibered-map m m'
  htpy-eq-fibered-map m .m refl = refl-htpy-fibered-map m

  is-torsorial-htpy-fibered-map :
    (m : fibered-map f g) → is-torsorial (htpy-fibered-map m)
  is-torsorial-htpy-fibered-map m =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-base-fibered-map f g m))
      ( map-base-fibered-map f g m , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-total-fibered-map f g m))
        ( map-total-fibered-map f g m , refl-htpy)
        ( is-torsorial-htpy
          ( is-map-over-map-total-fibered-map f g m ∙h refl-htpy)))

  is-equiv-htpy-eq-fibered-map :
    (m m' : fibered-map f g) → is-equiv (htpy-eq-fibered-map m m')
  is-equiv-htpy-eq-fibered-map m =
    fundamental-theorem-id
      ( is-torsorial-htpy-fibered-map m)
      ( htpy-eq-fibered-map m)

  extensionality-fibered-map :
    (m m' : fibered-map f g) → (m ＝ m') ≃ (htpy-fibered-map m m')
  pr1 (extensionality-fibered-map m m') = htpy-eq-fibered-map m m'
  pr2 (extensionality-fibered-map m m') = is-equiv-htpy-eq-fibered-map m m'

  eq-htpy-fibered-map :
    (m m' : fibered-map f g) → htpy-fibered-map m m' → m ＝ m'
  eq-htpy-fibered-map m m' = map-inv-equiv (extensionality-fibered-map m m')
```

### Fibered maps and fiberwise maps over are equivalent notions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y)
  where

  fiberwise-map-over-map-over :
    map-over f g i → fiberwise-map-over f g i
  pr1 (fiberwise-map-over-map-over (h , H) .(f a) (a , refl)) = h a
  pr2 (fiberwise-map-over-map-over (h , H) .(f a) (a , refl)) = inv (H a)

  map-over-fiberwise-map-over :
    fiberwise-map-over f g i → map-over f g i
  pr1 (map-over-fiberwise-map-over α) a = pr1 (α (f a) (pair a refl))
  pr2 (map-over-fiberwise-map-over α) a = inv (pr2 (α (f a) (pair a refl)))

  is-section-map-over-fiberwise-map-over-eq-htpy :
    (α : fiberwise-map-over f g i) (x : X) →
    fiberwise-map-over-map-over (map-over-fiberwise-map-over α) x ~ α x
  is-section-map-over-fiberwise-map-over-eq-htpy α .(f a) (pair a refl) =
    eq-pair-eq-fiber (inv-inv (pr2 (α (f a) (pair a refl))))

  is-section-map-over-fiberwise-map-over :
    fiberwise-map-over-map-over ∘ map-over-fiberwise-map-over ~ id
  is-section-map-over-fiberwise-map-over α =
    eq-htpy (eq-htpy ∘ is-section-map-over-fiberwise-map-over-eq-htpy α)

  is-retraction-map-over-fiberwise-map-over :
    map-over-fiberwise-map-over ∘ fiberwise-map-over-map-over ~ id
  is-retraction-map-over-fiberwise-map-over (pair h H) =
    eq-pair-eq-fiber (eq-htpy (inv-inv ∘ H))

  abstract
    is-equiv-fiberwise-map-over-map-over :
      is-equiv (fiberwise-map-over-map-over)
    is-equiv-fiberwise-map-over-map-over =
      is-equiv-is-invertible
        ( map-over-fiberwise-map-over)
        ( is-section-map-over-fiberwise-map-over)
        ( is-retraction-map-over-fiberwise-map-over)

  abstract
    is-equiv-map-over-fiberwise-map-over :
      is-equiv (map-over-fiberwise-map-over)
    is-equiv-map-over-fiberwise-map-over =
      is-equiv-is-invertible
        ( fiberwise-map-over-map-over)
        ( is-retraction-map-over-fiberwise-map-over)
        ( is-section-map-over-fiberwise-map-over)

  equiv-fiberwise-map-over-map-over :
    map-over f g i ≃ fiberwise-map-over f g i
  pr1 equiv-fiberwise-map-over-map-over =
    fiberwise-map-over-map-over
  pr2 equiv-fiberwise-map-over-map-over =
    is-equiv-fiberwise-map-over-map-over

  equiv-map-over-fiberwise-map-over :
    fiberwise-map-over f g i ≃ map-over f g i
  pr1 equiv-map-over-fiberwise-map-over =
    map-over-fiberwise-map-over
  pr2 equiv-map-over-fiberwise-map-over =
    is-equiv-map-over-fiberwise-map-over

  equiv-map-over-fiberwise-hom :
    fiberwise-hom (i ∘ f) g ≃ map-over f g i
  equiv-map-over-fiberwise-hom =
    equiv-hom-slice-fiberwise-hom (i ∘ f) g

  equiv-fiberwise-map-over-fiberwise-hom :
    fiberwise-hom (i ∘ f) g ≃ fiberwise-map-over f g i
  equiv-fiberwise-map-over-fiberwise-hom =
    equiv-fiberwise-map-over-map-over ∘e equiv-map-over-fiberwise-hom

  is-small-fiberwise-map-over :
    is-small (l1 ⊔ l2 ⊔ l4) (fiberwise-map-over f g i)
  pr1 is-small-fiberwise-map-over = map-over f g i
  pr2 is-small-fiberwise-map-over = equiv-map-over-fiberwise-map-over
```

### Slice maps are equal to fibered maps over

```agda
eq-map-over-id-hom-slice :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g ＝ map-over f g id
eq-map-over-id-hom-slice f g = refl

eq-map-over-hom-slice :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (i : X → Y) → hom-slice (i ∘ f) g ＝ map-over f g i
eq-map-over-hom-slice f g i = refl
```

### Horizontal composition for fibered maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  {f : A → X} {g : B → Y} {h : C → Z}
  where

  is-map-over-pasting-horizontal :
    {k : X → Y} {l : Y → Z} {i : A → B} {j : B → C} →
    is-map-over f g k i → is-map-over g h l j →
    is-map-over f h (l ∘ k) (j ∘ i)
  is-map-over-pasting-horizontal {k} {l} {i} {j} =
    pasting-horizontal-coherence-square-maps i j f g h k l

  map-over-pasting-horizontal :
    {k : X → Y} {l : Y → Z} →
    map-over f g k → map-over g h l → map-over f h (l ∘ k)
  pr1 (map-over-pasting-horizontal {k} {l} (i , I) (j , J)) = j ∘ i
  pr2 (map-over-pasting-horizontal {k} {l} (i , I) (j , J)) =
    is-map-over-pasting-horizontal {k} {l} I J

  fibered-map-pasting-horizontal :
    fibered-map f g → fibered-map g h → fibered-map f h
  pr1 (fibered-map-pasting-horizontal (k , iI) (l , jJ)) = l ∘ k
  pr2 (fibered-map-pasting-horizontal (k , iI) (l , jJ)) =
    map-over-pasting-horizontal {k} {l} iI jJ
```

### Vertical composition for fibered maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2}
  {C : UU l3} {D : UU l4}
  {X : UU l5} {Y : UU l6}
  {i : A → B} {j : C → D} {k : X → Y}
  where

  is-map-over-pasting-vertical :
    {f : A → C} {g : B → D}
    {f' : C → X} {g' : D → Y} →
    is-map-over f g j i → is-map-over f' g' k j →
    is-map-over (f' ∘ f) (g' ∘ g) k i
  is-map-over-pasting-vertical {f} {g} {f'} {g'} =
    pasting-vertical-coherence-square-maps i f g j f' g' k
```

### The truncation level of the types of fibered maps is bounded by the truncation level of the codomains

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-trunc-is-map-over :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y →
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) →
    is-trunc k (is-map-over f g i h)
  is-trunc-is-map-over k is-trunc-Y f g i h =
    is-trunc-Π k (λ x → is-trunc-Y (i (f x)) (g (h x)))

  is-trunc-map-over :
    (k : 𝕋) → is-trunc (succ-𝕋 k) Y → is-trunc k B →
    (f : A → X) (g : B → Y) (i : X → Y) → is-trunc k (map-over f g i)
  is-trunc-map-over k is-trunc-Y is-trunc-B f g i =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-B)
      ( is-trunc-is-map-over k is-trunc-Y f g i)

  is-trunc-fibered-map :
    (k : 𝕋) → is-trunc k Y → is-trunc k B →
    (f : A → X) (g : B → Y) → is-trunc k (fibered-map f g)
  is-trunc-fibered-map k is-trunc-Y is-trunc-B f g =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-Y)
      ( is-trunc-map-over
        ( k)
        ( is-trunc-succ-is-trunc k is-trunc-Y)
        ( is-trunc-B)
        ( f)
        ( g))
```

### The transpose of a fibered map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  transpose-is-map-over :
    (f : A → X) (g : B → Y) (i : X → Y) (h : A → B) →
    is-map-over f g i h → is-map-over h i g f
  transpose-is-map-over f g i h = inv-htpy

  transpose-map-over :
    (f : A → X) (g : B → Y) (i : X → Y)
    (hH : map-over f g i) → map-over (pr1 hH) i g
  pr1 (transpose-map-over f g i hH) = f
  pr2 (transpose-map-over f g i (h , H)) =
    transpose-is-map-over f g i h H

  transpose-fibered-map :
    (f : A → X) (g : B → Y)
    (ihH : fibered-map f g) → fibered-map (pr1 (pr2 ihH)) (pr1 ihH)
  pr1 (transpose-fibered-map f g ihH) = g
  pr2 (transpose-fibered-map f g (i , hH)) =
    transpose-map-over f g i hH
```

### If the top left corner is empty, the type of fibered maps is equivalent to maps `X → Y`

```text
         !
  empty ---> B
    |        |
  ! |        | g
    ∨        ∨
    X -----> Y
        i
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (is-empty-A : is-empty A)
  where

  inv-compute-fibered-map-is-empty : (fibered-map f g) ≃ (X → Y)
  inv-compute-fibered-map-is-empty =
    right-unit-law-Σ-is-contr
      ( λ i →
        is-contr-Σ
          ( universal-property-empty-is-empty A is-empty-A B)
          ( ex-falso ∘ is-empty-A)
          ( dependent-universal-property-empty-is-empty A is-empty-A
            ( eq-value (i ∘ f) (g ∘ ex-falso ∘ is-empty-A))))

  compute-fibered-map-is-empty : (X → Y) ≃ (fibered-map f g)
  compute-fibered-map-is-empty = inv-equiv inv-compute-fibered-map-is-empty

module _
  { l2 l3 l4 : Level} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : empty → X} (g : B → Y)
  where

  inv-compute-fibered-map-empty : (fibered-map f g) ≃ (X → Y)
  inv-compute-fibered-map-empty = inv-compute-fibered-map-is-empty f g id

  compute-fibered-map-empty : (X → Y) ≃ (fibered-map f g)
  compute-fibered-map-empty = compute-fibered-map-is-empty f g id
```

### If the bottom right corner is contractible, the type of fibered maps is equivalent to maps `A → B`

```text
    A -----> B
    |        |
  f |        | !
    ∨        ∨
    X ---> unit
       !
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y) (is-contr-Y : is-contr Y)
  where

  inv-compute-fibered-map-is-contr : (fibered-map f g) ≃ (A → B)
  inv-compute-fibered-map-is-contr =
    ( right-unit-law-Σ-is-contr
      ( λ j →
        is-contr-Π
          ( λ x →
            is-prop-is-contr is-contr-Y (center is-contr-Y) (g (j x))))) ∘e
    ( left-unit-law-Σ-is-contr
      ( is-contr-function-type is-contr-Y)
      ( λ _ → center is-contr-Y))

  compute-fibered-map-is-contr : (A → B) ≃ (fibered-map f g)
  compute-fibered-map-is-contr = inv-equiv inv-compute-fibered-map-is-contr

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) {g : B → unit}
  where

  inv-compute-fibered-map-unit : (fibered-map f g) ≃ (A → B)
  inv-compute-fibered-map-unit =
    inv-compute-fibered-map-is-contr f g is-contr-unit

  compute-fibered-map-unit : (A → B) ≃ (fibered-map f g)
  compute-fibered-map-unit = compute-fibered-map-is-contr f g is-contr-unit
```

## Examples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (h : A → B)
  where

  is-fibered-over-self : is-map-over id id h h
  is-fibered-over-self = refl-htpy

  self-map-over : map-over id id h
  pr1 self-map-over = h
  pr2 self-map-over = is-fibered-over-self

  self-fibered-map : fibered-map id id
  pr1 self-fibered-map = h
  pr2 self-fibered-map = self-map-over

  is-map-over-id : is-map-over h h id id
  is-map-over-id = refl-htpy

  id-map-over : map-over h h id
  pr1 id-map-over = id
  pr2 id-map-over = is-map-over-id

  id-fibered-map : fibered-map h h
  pr1 id-fibered-map = id
  pr2 id-fibered-map = id-map-over
```

## See also

- [Morphisms of arrows](foundation.morphisms-arrows.md) for the same concept
  under a different name.
- For the pullback property of the type of fibered maps, see
  [the pullback-hom](orthogonal-factorization-systems.pullback-hom.md)
