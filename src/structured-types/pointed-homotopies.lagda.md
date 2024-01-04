# Pointed homotopies

```agda
module structured-types.pointed-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "pointed homotopy"}} between [pointed dependent functions](structured-types.pointed-dependent-functions.md) is a pointed dependent
function of the [pointed family](structured-types.pointed-families-of-types.md) of [pointwise identifications](foundation-core.homotopies.md). More explicitly, a pointed homotopy `f ~∗ g` consists of a homotopy `H : f ~ g` between the underlying dependent functions, and an [identification](foundation-core.identity-types.md) witnessing that the triangle of identifications

```text
                f * ----> g *
                   \     /
  preserves-point f \   / preserves-point g
                     V V
                      *
```

[commutes](foundation.commuting-triangles-of-identifications.md).

Note that since pointed
homotopies are defined for pointed dependent functions, a pointed homotopy
between pointed homotopies is just an instance of a pointed homotopy.

## Definitions

### Pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  coherence-triangle-pointed-htpy :
    (g : pointed-Π A B) → function-pointed-Π f ~ function-pointed-Π g → UU l2
  coherence-triangle-pointed-htpy g G =
    G (point-Pointed-Type A) ＝
    ( preserves-point-function-pointed-Π f) ∙
    ( inv (preserves-point-function-pointed-Π g))

  pointed-htpy : pointed-Π A B → UU (l1 ⊔ l2)
  pointed-htpy g =
    pointed-Π A
      ( pair
        ( λ x →
          Id
            ( function-pointed-Π f x)
            ( function-pointed-Π g x))
        ( ( preserves-point-function-pointed-Π f) ∙
          ( inv (preserves-point-function-pointed-Π g))))

  _~∗_ : pointed-Π A B → UU (l1 ⊔ l2)
  _~∗_ = pointed-htpy
  
  infix 6 _~∗_

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (H : f ~∗ g)
  where

  htpy-pointed-htpy :
    function-pointed-Π f ~ function-pointed-Π g
  htpy-pointed-htpy = pr1 H

  coh-pointed-htpy :
    coherence-triangle-pointed-htpy f g htpy-pointed-htpy
  coh-pointed-htpy = pr2 H
```

## Properties

### Extensionality of pointed dependent function types

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  refl-pointed-htpy : f ~∗ f
  pr1 refl-pointed-htpy = refl-htpy
  pr2 refl-pointed-htpy = inv (right-inv (preserves-point-function-pointed-Π f))

  extensionality-pointed-Π : (g : pointed-Π A B) → Id f g ≃ pointed-htpy f g
  extensionality-pointed-Π =
    extensionality-Σ
      ( λ {g} q H →
        H (point-Pointed-Type A) ＝
        preserves-point-function-pointed-Π f ∙
        inv (preserves-point-function-pointed-Π (g , q)))
      ( refl-htpy)
      ( inv (right-inv (preserves-point-function-pointed-Π f)))
      ( λ g → equiv-funext)
      ( λ p →
        ( equiv-right-transpose-eq-concat
          ( refl)
          ( p)
          ( preserves-point-function-pointed-Π f)) ∘e
        ( equiv-inv (preserves-point-function-pointed-Π f) p))

  eq-pointed-htpy :
    (g : pointed-Π A B) → pointed-htpy f g → Id f g
  eq-pointed-htpy g = map-inv-equiv (extensionality-pointed-Π g)
```

### Pointed homotopies are equivalent to identifications of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  htpy-pointed-map : (g : A →∗ B) → UU (l1 ⊔ l2)
  htpy-pointed-map = pointed-htpy f

  extensionality-pointed-map : (g : A →∗ B) → Id f g ≃ (htpy-pointed-map g)
  extensionality-pointed-map = extensionality-pointed-Π f

  eq-htpy-pointed-map : (g : A →∗ B) → (htpy-pointed-map g) → Id f g
  eq-htpy-pointed-map g = map-inv-equiv (extensionality-pointed-map g)
```

### Concatenation of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  where

  htpy-concat-pointed-htpy :
    (f g h : pointed-Π A B) →
    pointed-htpy f g → pointed-htpy g h →
    function-pointed-Π f ~ function-pointed-Π h
  htpy-concat-pointed-htpy f g h G H =
    htpy-pointed-htpy f g G ∙h htpy-pointed-htpy g h H

  coh-concat-pointed-htpy :
    (f g h : pointed-Π A B) →
    (G : pointed-htpy f g) (H : pointed-htpy g h) →
    coherence-triangle-pointed-htpy f h (htpy-concat-pointed-htpy f g h G H)
  coh-concat-pointed-htpy f g h G H =
    ( horizontal-concat-Id² (coh-pointed-htpy f g G) (coh-pointed-htpy g h H)) ∙
    ( ( assoc
        ( preserves-point-function-pointed-Π f)
        ( inv (preserves-point-function-pointed-Π g))
        ( ( preserves-point-function-pointed-Π g) ∙
          ( inv (preserves-point-function-pointed-Π h)))) ∙
      ( ap
        ( concat
          ( preserves-point-function-pointed-Π f)
          ( function-pointed-Π h (point-Pointed-Type A)))
        ( ( inv
            ( assoc
              ( inv (preserves-point-function-pointed-Π g))
              ( preserves-point-function-pointed-Π g)
              ( inv (preserves-point-function-pointed-Π h)))) ∙
          ( ap
            ( concat'
              ( point-Pointed-Fam A B)
              ( inv (preserves-point-function-pointed-Π h)))
            ( left-inv (preserves-point-function-pointed-Π g))))))

  concat-pointed-htpy :
    (f g h : pointed-Π A B) →
    pointed-htpy f g → pointed-htpy g h → pointed-htpy f h
  pr1 (concat-pointed-htpy f g h G H) = htpy-concat-pointed-htpy f g h G H
  pr2 (concat-pointed-htpy f g h G H) = coh-concat-pointed-htpy f g h G H
```

### Inverses of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (H : pointed-htpy f g)
  where

  htpy-inv-pointed-htpy :
    function-pointed-Π g ~ function-pointed-Π f
  htpy-inv-pointed-htpy = inv-htpy (htpy-pointed-htpy f g H)

  coh-inv-pointed-htpy :
    coherence-triangle-pointed-htpy g f htpy-inv-pointed-htpy
  coh-inv-pointed-htpy =
    ( ap inv (coh-pointed-htpy f g H)) ∙
    ( ( distributive-inv-concat
        ( preserves-point-function-pointed-Π f)
        ( inv (preserves-point-function-pointed-Π g))) ∙
      ( ap
        ( concat'
          ( function-pointed-Π g (point-Pointed-Type A))
          ( inv (preserves-point-function-pointed-Π f)))
        ( inv-inv (preserves-point-function-pointed-Π g))))

  inv-pointed-htpy : pointed-htpy g f
  pr1 inv-pointed-htpy = htpy-inv-pointed-htpy
  pr2 inv-pointed-htpy = coh-inv-pointed-htpy
```

### Associativity of composition of pointed maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : Pointed-Type l3} {D : Pointed-Type l4}
  where

  htpy-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    map-comp-pointed-map (comp-pointed-map h g) f ~
    map-comp-pointed-map h (comp-pointed-map g f)
  htpy-associative-comp-pointed-map h g f = refl-htpy

  coh-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    coherence-triangle-pointed-htpy
      ( comp-pointed-map (comp-pointed-map h g) f)
      ( comp-pointed-map h (comp-pointed-map g f))
      ( htpy-associative-comp-pointed-map h g f)
  coh-associative-comp-pointed-map (pair h refl) (pair g refl) (pair f refl) =
    refl
    
  associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    htpy-pointed-map
      ( comp-pointed-map (comp-pointed-map h g) f)
      ( comp-pointed-map h (comp-pointed-map g f))
  pr1 (associative-comp-pointed-map h g f) =
    htpy-associative-comp-pointed-map h g f
  pr2 (associative-comp-pointed-map h g f) =
    coh-associative-comp-pointed-map h g f

  htpy-inv-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    map-pointed-map (comp-pointed-map h (comp-pointed-map g f)) ~
    map-pointed-map (comp-pointed-map (comp-pointed-map h g) f)
  htpy-inv-associative-comp-pointed-map h g f = refl-htpy

  coh-inv-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    coherence-triangle-pointed-htpy
      ( comp-pointed-map h (comp-pointed-map g f))
      ( comp-pointed-map (comp-pointed-map h g) f)
      ( htpy-inv-associative-comp-pointed-map h g f)
  coh-inv-associative-comp-pointed-map
    (pair h refl) (pair g refl) (pair f refl) = refl

  inv-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    htpy-pointed-map
      ( comp-pointed-map h (comp-pointed-map g f))
      ( comp-pointed-map (comp-pointed-map h g) f)
  pr1 (inv-associative-comp-pointed-map h g f) =
    htpy-associative-comp-pointed-map h g f
  pr2 (inv-associative-comp-pointed-map h g f) =
    coh-inv-associative-comp-pointed-map h g f
```

### The left unit law for composition of pointed maps

**Lemma.** For any pointed map `f : A →∗ B` there is a pointed homotopy `id ∘∗ f ~∗ f`.

**Proof.** The underlying homotopy of the asserted pointed homotopy is `refl-htpy`. Then we need to show that the triangle

```text

```

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  htpy-left-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-left-unit-law-comp-pointed-map = refl-htpy

  coh-left-unit-law-comp-pointed-map :
    coherence-triangle-pointed-htpy
      ( comp-pointed-map id-pointed-map f)
      ( f)
      ( htpy-left-unit-law-comp-pointed-map)
  coh-left-unit-law-comp-pointed-map =
    ( inv (right-inv (preserves-point-pointed-map f))) ∙
    ( ap
      ( concat'
        ( map-pointed-map f (point-Pointed-Type A))
        ( inv (preserves-point-pointed-map f)))
      ( ( inv (ap-id (preserves-point-pointed-map f))) ∙
        ( inv right-unit)))

  left-unit-law-comp-pointed-map :
    htpy-pointed-map (comp-pointed-map id-pointed-map f) f
  pr1 left-unit-law-comp-pointed-map = htpy-left-unit-law-comp-pointed-map
  pr2 left-unit-law-comp-pointed-map = coh-left-unit-law-comp-pointed-map

  htpy-inv-left-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-inv-left-unit-law-comp-pointed-map = refl-htpy

  coh-inv-left-unit-law-comp-pointed-map :
    coherence-triangle-pointed-htpy
      ( f)
      ( comp-pointed-map id-pointed-map f)
      ( htpy-inv-left-unit-law-comp-pointed-map)
  coh-inv-left-unit-law-comp-pointed-map =
    {!!}
```

### The right unit law for composition of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  htpy-right-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-right-unit-law-comp-pointed-map = refl-htpy

  coh-right-unit-law-comp-pointed-map :
    coherence-triangle-pointed-htpy
      ( f ∘∗ id-pointed-map)
      ( f)
      ( htpy-right-unit-law-comp-pointed-map)
  coh-right-unit-law-comp-pointed-map =
    inv (right-inv (preserves-point-pointed-map f))

  right-unit-law-comp-pointed-map :
    htpy-pointed-map (comp-pointed-map f id-pointed-map) f
  pr1 right-unit-law-comp-pointed-map =
    htpy-right-unit-law-comp-pointed-map
  pr2 right-unit-law-comp-pointed-map =
    coh-right-unit-law-comp-pointed-map
```
