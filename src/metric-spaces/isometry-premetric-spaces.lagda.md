# Isometries between premetric spaces

```agda
module metric-spaces.isometry-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
```

</details>

## Idea

A function between [premetric spaces](metric-spaces.premetric-spaces.md) is an
{{#concept "isometry" Disambiguation="between premetric spaces" Agda=is-isometry-Premetric-Space}}
if it preserves and reflects
[premetric structures](metric-spaces.premetric-structures.md).

The upper bounds on the distance between any two points and their image by an
isometry are the same.

## Definitions

### The property of being a isometry between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : function-carrier-type-Premetric-Space A B)
  where

  is-isometry-prop-Premetric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-isometry-prop-Premetric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Premetric-Space A)
          ( λ x →
            Π-Prop
              ( type-Premetric-Space A)
              ( λ y →
                iff-Prop
                  ( structure-Premetric-Space A d x y)
                  ( structure-Premetric-Space B d (f x) (f y)))))

  is-isometry-Premetric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-isometry-Premetric-Space =
    type-Prop is-isometry-prop-Premetric-Space

  is-prop-is-isometry-Premetric-Space : is-prop is-isometry-Premetric-Space
  is-prop-is-isometry-Premetric-Space =
    is-prop-type-Prop is-isometry-prop-Premetric-Space
```

### The type of isometries between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  isometry-Premetric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-Premetric-Space = type-subtype (is-isometry-prop-Premetric-Space A B)
```

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : isometry-Premetric-Space A B)
  where

  map-isometry-Premetric-Space : function-carrier-type-Premetric-Space A B
  map-isometry-Premetric-Space = pr1 f

  is-isometry-map-isometry-Premetric-Space :
    is-isometry-Premetric-Space A B map-isometry-Premetric-Space
  is-isometry-map-isometry-Premetric-Space = pr2 f
```

## Properties

### Equality of isometries in premetric spaces is characterized by homotopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f g : isometry-Premetric-Space A B)
  where

  equiv-eq-htpy-map-isometry-Premetric-Space :
    ( f ＝ g) ≃
    ( map-isometry-Premetric-Space A B f ~
      map-isometry-Premetric-Space A B g)
  equiv-eq-htpy-map-isometry-Premetric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-isometry-prop-Premetric-Space A B)
      ( f)
      ( g)

  eq-htpy-map-isometry-Premetric-Space :
    ( map-isometry-Premetric-Space A B f ~
      map-isometry-Premetric-Space A B g) →
    ( f ＝ g)
  eq-htpy-map-isometry-Premetric-Space =
    map-inv-equiv equiv-eq-htpy-map-isometry-Premetric-Space
```

### Composition of isometries between premetric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Premetric-Space l1a l2a)
  (B : Premetric-Space l1b l2b)
  (C : Premetric-Space l1c l2c)
  (g : function-carrier-type-Premetric-Space B C)
  (f : function-carrier-type-Premetric-Space A B)
  where

  preserves-isometry-comp-function-Premetric-Space :
    is-isometry-Premetric-Space B C g →
    is-isometry-Premetric-Space A B f →
    is-isometry-Premetric-Space A C (g ∘ f)
  preserves-isometry-comp-function-Premetric-Space H K d x y =
    (H d (f x) (f y)) ∘iff (K d x y)
```

### The inverse of an isometric equivalence between premetric spaces is isometric

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : function-carrier-type-Premetric-Space A B)
  (E : is-equiv f)
  (I : is-isometry-Premetric-Space A B f)
  where

  is-isometry-map-inv-is-equiv-is-isometry-Premetric-Space :
    is-isometry-Premetric-Space B A (map-inv-is-equiv E)
  is-isometry-map-inv-is-equiv-is-isometry-Premetric-Space d x y =
    logical-equivalence-reasoning
      ( neighborhood-Premetric-Space B d x y)
      ↔ ( neighborhood-Premetric-Space B d
          ( f (map-inv-is-equiv E x))
          ( f (map-inv-is-equiv E y)))
        by
          binary-tr
            ( λ u v →
              ( neighborhood-Premetric-Space B d x y) ↔
              ( neighborhood-Premetric-Space B d u v))
            ( inv (is-section-map-inv-is-equiv E x))
            ( inv (is-section-map-inv-is-equiv E y))
            ( id-iff)
      ↔ ( neighborhood-Premetric-Space A d
          ( map-inv-is-equiv E x)
          ( map-inv-is-equiv E y))
        by
          inv-iff
            ( I d (map-inv-is-equiv E x) (map-inv-is-equiv E y))
```
