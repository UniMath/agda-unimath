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

A pointed homotopy between pointed dependent functions is a pointed dependent
function of the pointed family of pointwise identifications. Since pointed
homotopies are defined for pointed dependent functions, a pointed homotopy
between pointed homotopies is just an instance of a pointed homotopy.

## Definitions

### Pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

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

  triangle-pointed-htpy :
    htpy-pointed-htpy (point-Pointed-Type A) ＝
    ( preserves-point-function-pointed-Π f) ∙
    ( inv (preserves-point-function-pointed-Π g))
  triangle-pointed-htpy = pr2 H
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

### The category laws for pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  left-unit-law-comp-pointed-map :
    htpy-pointed-map (comp-pointed-map id-pointed-map f) f
  left-unit-law-comp-pointed-map =
    pair
      ( refl-htpy)
      ( ( inv (right-inv (pr2 f))) ∙
        ( ap
          ( concat'
            ( map-pointed-map f (point-Pointed-Type A))
            ( inv (pr2 f)))
          ( ( inv (ap-id (pr2 f))) ∙
            ( inv right-unit))))

  right-unit-law-comp-pointed-map :
    htpy-pointed-map (comp-pointed-map f id-pointed-map) f
  right-unit-law-comp-pointed-map =
    pair
      ( refl-htpy)
      ( inv (right-inv (pr2 f)))

module _
  {l1 l2 l3 l4 : Level}
  where

  associative-comp-pointed-map :
    {A : Pointed-Type l1} {B : Pointed-Type l2}
    {C : Pointed-Type l3} {D : Pointed-Type l4}
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    htpy-pointed-map
      ( comp-pointed-map (comp-pointed-map h g) f)
      ( comp-pointed-map h (comp-pointed-map g f))
  associative-comp-pointed-map
    (pair h refl) (pair g refl) (pair f refl) =
    pair refl-htpy refl

  inv-associative-comp-pointed-map :
    {A : Pointed-Type l1} {B : Pointed-Type l2}
    {C : Pointed-Type l3} {D : Pointed-Type l4}
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    htpy-pointed-map
      ( comp-pointed-map h (comp-pointed-map g f))
      ( comp-pointed-map (comp-pointed-map h g) f)
  inv-associative-comp-pointed-map
    (pair h refl) (pair g refl) (pair f refl) =
    pair refl-htpy refl
```

### Concatenation of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  where

  concat-pointed-htpy :
    (f g h : pointed-Π A B) →
    pointed-htpy f g → pointed-htpy g h → pointed-htpy f h
  concat-pointed-htpy f g h G H =
    pair
      ( pr1 G ∙h pr1 H)
      ( ( ap-binary (λ p q → p ∙ q) (pr2 G) (pr2 H)) ∙
        ( ( assoc (pr2 f) (inv (pr2 g)) (pr2 g ∙ inv (pr2 h))) ∙
          ( ap
            ( concat (pr2 f) (function-pointed-Π h (point-Pointed-Type A)))
            ( ( inv (assoc (inv (pr2 g)) (pr2 g) (inv (pr2 h)))) ∙
              ( ap
                ( concat' (point-Pointed-Fam A B) (inv (pr2 h)))
                ( left-inv (pr2 g)))))))
```

### Inverses of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  where

  inv-pointed-htpy :
    (f g : pointed-Π A B) → pointed-htpy f g → pointed-htpy g f
  inv-pointed-htpy f g H =
    pair
      ( inv-htpy (pr1 H))
      ( ( ap inv (pr2 H)) ∙
        ( ( distributive-inv-concat (pr2 f) (inv (pr2 g))) ∙
          ( ap
            ( concat'
              ( function-pointed-Π g (point-Pointed-Type A))
              ( inv (pr2 f)))
            ( inv-inv (pr2 g)))))
```
