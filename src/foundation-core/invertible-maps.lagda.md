# Invertible maps

```agda
module foundation-core.invertible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

An {{#concept "inverse" Disambiguation="maps of types" Agda=is-inverse}} for a
map `f : A → B` is a map `g : B → A` equipped with
[homotopies](foundation-core.homotopies.md) `f ∘ g ~ id` and `g ∘ f ~ id`. Such
data, however, is [structure](foundation.structure.md) on the map `f`, and not
generally a [property](foundation-core.propositions.md).

## Definition

### The predicate that a map `g` is an inverse of a map `f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inverse : (A → B) → (B → A) → UU (l1 ⊔ l2)
  is-inverse f g = ((f ∘ g) ~ id) × ((g ∘ f) ~ id)

  is-section-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → f ∘ g ~ id
  is-section-is-inverse = pr1

  is-retraction-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → g ∘ f ~ id
  is-retraction-is-inverse = pr2
```

### The predicate that a map `f` is invertible

```agda
is-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-invertible {A = A} {B} f = Σ (B → A) (is-inverse f)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (g : is-invertible f)
  where

  map-inv-is-invertible : B → A
  map-inv-is-invertible = pr1 g

  is-inverse-map-inv-is-invertible : is-inverse f map-inv-is-invertible
  is-inverse-map-inv-is-invertible = pr2 g

  is-section-map-inv-is-invertible : f ∘ map-inv-is-invertible ~ id
  is-section-map-inv-is-invertible = pr1 is-inverse-map-inv-is-invertible

  is-retraction-map-inv-is-invertible : map-inv-is-invertible ∘ f ~ id
  is-retraction-map-inv-is-invertible = pr2 is-inverse-map-inv-is-invertible

  section-is-invertible : section f
  pr1 section-is-invertible = map-inv-is-invertible
  pr2 section-is-invertible = is-section-map-inv-is-invertible

  retraction-is-invertible : retraction f
  pr1 retraction-is-invertible = map-inv-is-invertible
  pr2 retraction-is-invertible = is-retraction-map-inv-is-invertible
```

### The type of invertible maps

```agda
invertible-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
invertible-map A B = Σ (A → B) (is-invertible)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-invertible-map : invertible-map A B → A → B
  map-invertible-map = pr1

  is-invertible-map-invertible-map :
    (f : invertible-map A B) → is-invertible (map-invertible-map f)
  is-invertible-map-invertible-map = pr2

  map-inv-invertible-map : invertible-map A B → B → A
  map-inv-invertible-map =
    map-inv-is-invertible ∘ is-invertible-map-invertible-map

  is-retraction-map-inv-invertible-map :
    (f : invertible-map A B) →
    map-inv-invertible-map f ∘ map-invertible-map f ~ id
  is-retraction-map-inv-invertible-map =
    is-retraction-map-inv-is-invertible ∘ is-invertible-map-invertible-map

  is-section-map-inv-invertible-map :
    (f : invertible-map A B) →
    map-invertible-map f ∘ map-inv-invertible-map f ~ id
  is-section-map-inv-invertible-map =
    is-section-map-inv-is-invertible ∘ is-invertible-map-invertible-map
```

## Properties

### The identity invertible map

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-inverse-id : is-inverse id (id {A = A})
  pr1 is-inverse-id = refl-htpy
  pr2 is-inverse-id = refl-htpy

  is-invertible-id : is-invertible (id {A = A})
  pr1 is-invertible-id = id
  pr2 is-invertible-id = is-inverse-id

  id-invertible-map : invertible-map A A
  pr1 id-invertible-map = id
  pr2 id-invertible-map = is-invertible-id
```

### The inverse of an invertible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inverse-inv-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → is-inverse g f
  pr1 (is-inverse-inv-is-inverse {f} {g} H) =
    is-retraction-map-inv-is-invertible (g , H)
  pr2 (is-inverse-inv-is-inverse {f} {g} H) =
    is-section-map-inv-is-invertible (g , H)

  is-invertible-map-inv-is-invertible :
    {f : A → B} (g : is-invertible f) → is-invertible (map-inv-is-invertible g)
  pr1 (is-invertible-map-inv-is-invertible {f} g) = f
  pr2 (is-invertible-map-inv-is-invertible {f} g) =
    is-inverse-inv-is-inverse {f} (is-inverse-map-inv-is-invertible g)

  is-invertible-map-inv-invertible-map :
    (f : invertible-map A B) → is-invertible (map-inv-invertible-map f)
  is-invertible-map-inv-invertible-map f =
    is-invertible-map-inv-is-invertible (is-invertible-map-invertible-map f)

  inv-invertible-map : invertible-map A B → invertible-map B A
  pr1 (inv-invertible-map f) = map-inv-invertible-map f
  pr2 (inv-invertible-map f) = is-invertible-map-inv-invertible-map f
```

### The inversion operation on invertible maps is a strict involution

The inversion operation on invertible maps is a strict involution, where, by
strict involution, we mean that `inv-invertible-map (inv-invertible-map f) ≐ f`
syntactically. This can be observed by the fact that the type-checker accepts
`refl` as proof of this equation.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-involution-inv-invertible-map :
    {f : invertible-map A B} → inv-invertible-map (inv-invertible-map f) ＝ f
  is-involution-inv-invertible-map = refl
```

### Composition of invertible maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (G : is-invertible g) (F : is-invertible f)
  where

  map-inv-is-invertible-comp : C → A
  map-inv-is-invertible-comp =
    map-inv-is-invertible F ∘ map-inv-is-invertible G

  is-section-map-inv-is-invertible-comp :
    is-section (g ∘ f) map-inv-is-invertible-comp
  is-section-map-inv-is-invertible-comp =
    is-section-map-section-comp g f
      ( section-is-invertible F)
      ( section-is-invertible G)

  is-retraction-map-inv-is-invertible-comp :
    is-retraction (g ∘ f) map-inv-is-invertible-comp
  is-retraction-map-inv-is-invertible-comp =
    is-retraction-map-retraction-comp g f
      ( retraction-is-invertible G)
      ( retraction-is-invertible F)

  is-invertible-comp : is-invertible (g ∘ f)
  is-invertible-comp =
    ( map-inv-is-invertible-comp ,
      is-section-map-inv-is-invertible-comp ,
      is-retraction-map-inv-is-invertible-comp)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-invertible-map-comp-invertible-map :
    (g : invertible-map B C) (f : invertible-map A B) →
    is-invertible (map-invertible-map g ∘ map-invertible-map f)
  is-invertible-map-comp-invertible-map g f =
    is-invertible-comp
      ( map-invertible-map g)
      ( map-invertible-map f)
      ( is-invertible-map-invertible-map g)
      ( is-invertible-map-invertible-map f)

  comp-invertible-map :
    invertible-map B C → invertible-map A B → invertible-map A C
  pr1 (comp-invertible-map g f) = map-invertible-map g ∘ map-invertible-map f
  pr2 (comp-invertible-map g f) = is-invertible-map-comp-invertible-map g f
```

### Invertible maps are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-section-map-inv-is-invertible-htpy :
    {f f' : A → B} (H : f' ~ f) (F : is-invertible f) →
    is-section f' (map-inv-is-invertible F)
  is-section-map-inv-is-invertible-htpy H (g , S , R) = H ·r g ∙h S

  is-retraction-map-inv-is-invertible-htpy :
    {f f' : A → B} (H : f' ~ f) (F : is-invertible f) →
    is-retraction f' (map-inv-is-invertible F)
  is-retraction-map-inv-is-invertible-htpy H (g , S , R) = g ·l H ∙h R

  is-invertible-htpy :
    {f f' : A → B} → f' ~ f → is-invertible f → is-invertible f'
  is-invertible-htpy H F =
    ( map-inv-is-invertible F ,
      is-section-map-inv-is-invertible-htpy H F ,
      is-retraction-map-inv-is-invertible-htpy H F)

  is-invertible-inv-htpy :
    {f f' : A → B} → f ~ f' → is-invertible f → is-invertible f'
  is-invertible-inv-htpy H = is-invertible-htpy (inv-htpy H)

  htpy-map-inv-is-invertible :
    {f g : A → B} (H : f ~ g) (F : is-invertible f) (G : is-invertible g) →
    map-inv-is-invertible F ~ map-inv-is-invertible G
  htpy-map-inv-is-invertible H F G =
    ( ( inv-htpy (is-retraction-map-inv-is-invertible G)) ·r
      ( map-inv-is-invertible F)) ∙h
    ( ( map-inv-is-invertible G) ·l
      ( ( inv-htpy H ·r map-inv-is-invertible F) ∙h
        ( is-section-map-inv-is-invertible F)))
```

### Any section of an invertible map is homotopic to its inverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : invertible-map A B)
  where

  htpy-map-inv-invertible-map-section :
    (f : section (map-invertible-map e)) →
    map-inv-invertible-map e ~
    map-section (map-invertible-map e) f
  htpy-map-inv-invertible-map-section (f , H) =
    ( map-inv-invertible-map e ·l inv-htpy H) ∙h
    ( is-retraction-map-inv-invertible-map e ·r f)
```

### Any retraction of an invertible map is homotopic to its inverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : invertible-map A B)
  where

  htpy-map-inv-invertible-map-retraction :
    (f : retraction (map-invertible-map e)) →
    map-inv-invertible-map e ~
    map-retraction (map-invertible-map e) f
  htpy-map-inv-invertible-map-retraction (f , H) =
    ( inv-htpy H ·r map-inv-invertible-map e) ∙h
    ( f ·l is-section-map-inv-invertible-map e)
```

### Invertible maps are injective

The construction of the converse map of the
[action on identifications](foundation.action-on-identifications-functions.md)
is a rerun of the proof that maps with
[retractions](foundation-core.retractions.md) are
[injective](foundation-core.injective-maps.md) (`is-injective-retraction`). We
repeat the proof to avoid cyclic dependencies.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-invertible f)
  where

  is-injective-is-invertible : {x y : A} → f x ＝ f y → x ＝ y
  is-injective-is-invertible =
    is-injective-retraction f (retraction-is-invertible H)
```

## See also

- For the coherent notion of invertible maps see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
