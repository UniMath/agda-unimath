# Pointed homotopies

```agda
module structured-types.pointed-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
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
function of the [pointed family](structured-types.pointed-families-of-types.md) of [pointwise identifications](foundation-core.homotopies.md). The base point of the family `x ↦ f x ＝ g x` over `A` is the identification

```text
  preserves-point f ∙ inv (preserves-point g) : f * ＝ g *.
```

A pointed homotopy `f ~∗ g` therefore consists of a homotopy `H : f ~ g` between the underlying dependent functions, and an [identification](foundation-core.identity-types.md) witnessing that the triangle of identifications

```text
                     H *
                f * ----> g *
                   \     ∧
  preserves-point f \   / inv (preserves-point g)
                     ∨ /
                      *
```

[commutes](foundation.commuting-triangles-of-identifications.md).

Note that since pointed
homotopies are defined for pointed dependent functions, a pointed homotopy
between pointed homotopies is just an instance of a pointed homotopy. A minor nuissance of this approach to the definition of pointed homotopies is that the commuting triangle in a pointed homotopy is slightly more complicated than the simpler triangle

```text
                f * ----> g *
                   \     /
  preserves-point f \   / preserves-point g
                     ∨ ∨
                      *.

```

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
    coherence-triangle-identifications
      ( G (point-Pointed-Type A))
      ( inv (preserves-point-function-pointed-Π g))
      ( preserves-point-function-pointed-Π f)

  coherence-triangle-pointed-htpy' :
    (g : pointed-Π A B) → function-pointed-Π f ~ function-pointed-Π g → UU l2
  coherence-triangle-pointed-htpy' g G =
    coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( G (point-Pointed-Type A))

  eq-value-function-pointed-Π :
    pointed-Π A B → Pointed-Fam l2 A
  pr1 (eq-value-function-pointed-Π g) =
    eq-value (function-pointed-Π f) (function-pointed-Π g)
  pr2 (eq-value-function-pointed-Π g) =
    ( preserves-point-function-pointed-Π f) ∙
    ( inv (preserves-point-function-pointed-Π g))

  pointed-htpy : pointed-Π A B → UU (l1 ⊔ l2)
  pointed-htpy g = pointed-Π A (eq-value-function-pointed-Π g)

  _~∗_ : pointed-Π A B → UU (l1 ⊔ l2)
  _~∗_ = pointed-htpy

  make-pointed-htpy :
    (g : pointed-Π A B) →
    (G : function-pointed-Π f ~ function-pointed-Π g) →
    coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( G (point-Pointed-Type A)) →
    pointed-htpy g
  pr1 (make-pointed-htpy g G p) = G
  pr2 (make-pointed-htpy g G p) =
    right-transpose-eq-concat
      ( G (point-Pointed-Type A))
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π f)
      ( inv p)
  
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

  coh-pointed-htpy' :
    coherence-triangle-pointed-htpy' f g htpy-pointed-htpy
  coh-pointed-htpy' =
    inv
      ( map-inv-is-equiv
        ( is-equiv-right-transpose-eq-concat _ _ _)
        ( coh-pointed-htpy))
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
  (f g h : pointed-Π A B) (G : pointed-htpy f g) (H : pointed-htpy g h)
  where

  htpy-concat-pointed-htpy :
    function-pointed-Π f ~ function-pointed-Π h
  htpy-concat-pointed-htpy =
    htpy-pointed-htpy f g G ∙h htpy-pointed-htpy g h H

  coh-concat-pointed-htpy' :
    coherence-triangle-pointed-htpy' f h htpy-concat-pointed-htpy
  coh-concat-pointed-htpy' =
    ( coh-pointed-htpy' f g G) ∙
    ( ( ap
        ( concat (htpy-pointed-htpy f g G (pr2 A)) _)
        ( coh-pointed-htpy' g h H)) ∙
      ( inv
        ( assoc
          ( htpy-pointed-htpy f g G (point-Pointed-Type A))
          ( htpy-pointed-htpy g h H (point-Pointed-Type A))
          ( preserves-point-function-pointed-Π h))))

  concat-pointed-htpy : pointed-htpy f h
  concat-pointed-htpy =
    make-pointed-htpy f h htpy-concat-pointed-htpy coh-concat-pointed-htpy'
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

  coh-inv-pointed-htpy' :
    coherence-triangle-pointed-htpy' g f htpy-inv-pointed-htpy
  coh-inv-pointed-htpy' =
    left-transpose-eq-concat
      ( htpy-pointed-htpy f g H (point-Pointed-Type A))
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π f)
      ( inv (coh-pointed-htpy' f g H))

  inv-pointed-htpy : pointed-htpy g f
  inv-pointed-htpy =
    make-pointed-htpy g f htpy-inv-pointed-htpy coh-inv-pointed-htpy'
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
  coh-associative-comp-pointed-map (h , refl) (g , refl) (f , refl) =
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
  coh-inv-associative-comp-pointed-map (h , refl) (g , refl) (f , refl) = refl

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

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  htpy-left-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-left-unit-law-comp-pointed-map = refl-htpy

  coh-left-unit-law-comp-pointed-map' :
    coherence-triangle-pointed-htpy'
      ( id-pointed-map ∘∗ f)
      ( f)
      ( htpy-left-unit-law-comp-pointed-map)
  coh-left-unit-law-comp-pointed-map' =
    right-unit ∙ ap-id (preserves-point-pointed-map f)

  left-unit-law-comp-pointed-map :
    htpy-pointed-map (id-pointed-map ∘∗ f) f
  left-unit-law-comp-pointed-map =
    make-pointed-htpy
      ( id-pointed-map ∘∗ f)
      ( f)
      ( htpy-left-unit-law-comp-pointed-map)
      ( coh-left-unit-law-comp-pointed-map')

  htpy-inv-left-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-inv-left-unit-law-comp-pointed-map = refl-htpy

  coh-inv-left-unit-law-comp-pointed-map' :
    coherence-triangle-pointed-htpy'
      ( f)
      ( comp-pointed-map id-pointed-map f)
      ( htpy-inv-left-unit-law-comp-pointed-map)
  coh-inv-left-unit-law-comp-pointed-map' =
    inv (right-unit ∙ ap-id (preserves-point-pointed-map f))

  inv-left-unit-law-comp-pointed-map :
    f ~∗ id-pointed-map ∘∗ f
  inv-left-unit-law-comp-pointed-map =
    make-pointed-htpy
      ( f)
      ( id-pointed-map ∘∗ f)
      ( htpy-inv-left-unit-law-comp-pointed-map)
      ( coh-inv-left-unit-law-comp-pointed-map')
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
