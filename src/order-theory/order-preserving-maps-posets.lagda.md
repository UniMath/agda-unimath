# Order preserving maps between posets

```agda
module order-theory.order-preserving-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.order-preserving-maps-preorders
open import order-theory.posets
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[posets](order-theory.posets.md) is said to be
{{#concept "order preserving" WD="increasing function" WDID=Q3075182 Agda=hom-Poset Disambiguation="map between posets"}}
if `x ≤ y` in `P` implies `f x ≤ f y` in `Q`.

## Definition

### Order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  preserves-order-prop-Poset :
    (type-Poset P → type-Poset Q) → Prop (l1 ⊔ l2 ⊔ l4)
  preserves-order-prop-Poset =
    preserves-order-prop-Preorder (preorder-Poset P) (preorder-Poset Q)

  preserves-order-Poset :
    (type-Poset P → type-Poset Q) → UU (l1 ⊔ l2 ⊔ l4)
  preserves-order-Poset =
    preserves-order-Preorder (preorder-Poset P) (preorder-Poset Q)

  is-prop-preserves-order-Poset :
    (f : type-Poset P → type-Poset Q) → is-prop (preserves-order-Poset f)
  is-prop-preserves-order-Poset =
    is-prop-preserves-order-Preorder (preorder-Poset P) (preorder-Poset Q)

  hom-set-Poset : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-set-Poset =
    set-subset
      ( function-Set (type-Poset P) (set-Poset Q))
      ( preserves-order-prop-Poset)

  hom-Poset : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Poset = type-Set hom-set-Poset

  map-hom-Poset : hom-Poset → type-Poset P → type-Poset Q
  map-hom-Poset = map-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  preserves-order-hom-Poset :
    (f : hom-Poset) → preserves-order-Poset (map-hom-Poset f)
  preserves-order-hom-Poset =
    preserves-order-hom-Preorder (preorder-Poset P) (preorder-Poset Q)
```

### Homotopies of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-hom-Poset : (f g : hom-Poset P Q) → UU (l1 ⊔ l3)
  htpy-hom-Poset = htpy-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  refl-htpy-hom-Poset : (f : hom-Poset P Q) → htpy-hom-Poset f f
  refl-htpy-hom-Poset =
    refl-htpy-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  htpy-eq-hom-Poset :
    (f g : hom-Poset P Q) → Id f g → htpy-hom-Poset f g
  htpy-eq-hom-Poset = htpy-eq-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  is-torsorial-htpy-hom-Poset :
    (f : hom-Poset P Q) → is-torsorial (htpy-hom-Poset f)
  is-torsorial-htpy-hom-Poset =
    is-torsorial-htpy-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  is-equiv-htpy-eq-hom-Poset :
    (f g : hom-Poset P Q) → is-equiv (htpy-eq-hom-Poset f g)
  is-equiv-htpy-eq-hom-Poset =
    is-equiv-htpy-eq-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  extensionality-hom-Poset :
    (f g : hom-Poset P Q) → Id f g ≃ htpy-hom-Poset f g
  extensionality-hom-Poset =
    extensionality-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  eq-htpy-hom-Poset :
    (f g : hom-Poset P Q) → htpy-hom-Poset f g → Id f g
  eq-htpy-hom-Poset = eq-htpy-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  is-prop-htpy-hom-Poset :
    (f g : hom-Poset P Q) → is-prop (htpy-hom-Poset f g)
  is-prop-htpy-hom-Poset f g =
    is-prop-Π
      ( λ x →
        is-set-type-Poset Q
          ( map-hom-Poset P Q f x)
          ( map-hom-Poset P Q g x))
```

### The identity order preserving map

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  preserves-order-id-Poset :
    preserves-order-Poset P P (id {A = type-Poset P})
  preserves-order-id-Poset = preserves-order-id-Preorder (preorder-Poset P)

  id-hom-Poset : hom-Poset P P
  id-hom-Poset = id-hom-Preorder (preorder-Poset P)
```

### Composing order preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4) (R : Poset l5 l6)
  where

  preserves-order-comp-Poset :
    (g : hom-Poset Q R) (f : hom-Poset P Q) →
    preserves-order-Poset P R
      ( map-hom-Poset Q R g ∘ map-hom-Poset P Q f)
  preserves-order-comp-Poset =
    preserves-order-comp-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)

  comp-hom-Poset :
    (g : hom-Poset Q R) (f : hom-Poset P Q) → hom-Poset P R
  comp-hom-Poset =
    comp-hom-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)
```

### Unit laws for composition of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  left-unit-law-comp-hom-Poset :
    (f : hom-Poset P Q) →
    Id ( comp-hom-Poset P Q Q (id-hom-Poset Q) f) f
  left-unit-law-comp-hom-Poset =
    left-unit-law-comp-hom-Preorder (preorder-Poset P) (preorder-Poset Q)

  right-unit-law-comp-hom-Poset :
    (f : hom-Poset P Q) →
    Id (comp-hom-Poset P P Q f (id-hom-Poset P)) f
  right-unit-law-comp-hom-Poset =
    right-unit-law-comp-hom-Preorder (preorder-Poset P) (preorder-Poset Q)
```

### Associativity of composition of order preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (R : Poset l5 l6) (S : Poset l7 l8)
  where

  associative-comp-hom-Poset :
    (h : hom-Poset R S) (g : hom-Poset Q R) (f : hom-Poset P Q) →
    comp-hom-Poset P Q S (comp-hom-Poset Q R S h g) f ＝
    comp-hom-Poset P R S h (comp-hom-Poset P Q R g f)
  associative-comp-hom-Poset =
    associative-comp-hom-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)
      ( preorder-Poset S)

  involutive-eq-associative-comp-hom-Poset :
    (h : hom-Poset R S) (g : hom-Poset Q R) (f : hom-Poset P Q) →
    comp-hom-Poset P Q S (comp-hom-Poset Q R S h g) f ＝ⁱ
    comp-hom-Poset P R S h (comp-hom-Poset P Q R g f)
  involutive-eq-associative-comp-hom-Poset =
    involutive-eq-associative-comp-hom-Preorder
      ( preorder-Poset P)
      ( preorder-Poset Q)
      ( preorder-Poset R)
      ( preorder-Poset S)
```
