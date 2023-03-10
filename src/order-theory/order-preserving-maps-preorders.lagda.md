# Order preserving maps on preorders

```agda
module order-theory.order-preserving-maps-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two preorders is siad to be order preserving if `x ≤ y` in `P` implies `f x ≤ f y` in `Q`.

## Definition

### Order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  preserves-order-preorder-Prop :
    (element-Preorder P → element-Preorder Q) → Prop (l1 ⊔ l2 ⊔ l4)
  preserves-order-preorder-Prop f =
    Π-Prop
      ( element-Preorder P)
      ( λ x →
        Π-Prop
          ( element-Preorder P)
          ( λ y →
            hom-Prop
              ( leq-preorder-Prop P x y)
              ( leq-preorder-Prop Q (f x) (f y))))

  preserves-order-Preorder :
    (element-Preorder P → element-Preorder Q) → UU (l1 ⊔ l2 ⊔ l4)
  preserves-order-Preorder f =
    type-Prop (preserves-order-preorder-Prop f)

  is-prop-preserves-order-Preorder :
    (f : element-Preorder P → element-Preorder Q) →
    is-prop (preserves-order-Preorder f)
  is-prop-preserves-order-Preorder f =
    is-prop-type-Prop (preserves-order-preorder-Prop f)

  hom-Preorder : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Preorder =
    Σ (element-Preorder P → element-Preorder Q) preserves-order-Preorder

  map-hom-Preorder : hom-Preorder → element-Preorder P → element-Preorder Q
  map-hom-Preorder = pr1

  preserves-order-map-hom-Preorder :
    (f : hom-Preorder) → preserves-order-Preorder (map-hom-Preorder f)
  preserves-order-map-hom-Preorder = pr2
```

### Homotopies of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  htpy-hom-Preorder : (f g : hom-Preorder P Q) → UU (l1 ⊔ l3)
  htpy-hom-Preorder f g = map-hom-Preorder P Q f ~ map-hom-Preorder P Q g

  refl-htpy-hom-Preorder : (f : hom-Preorder P Q) → htpy-hom-Preorder f f
  refl-htpy-hom-Preorder f = refl-htpy

  htpy-eq-hom-Preorder :
    (f g : hom-Preorder P Q) → Id f g → htpy-hom-Preorder f g
  htpy-eq-hom-Preorder f .f refl = refl-htpy-hom-Preorder f

  is-contr-total-htpy-hom-Preorder :
    (f : hom-Preorder P Q) →
    is-contr (Σ (hom-Preorder P Q) (htpy-hom-Preorder f))
  is-contr-total-htpy-hom-Preorder f =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (map-hom-Preorder P Q f))
      ( is-prop-preserves-order-Preorder P Q)
      ( map-hom-Preorder P Q f)
      ( refl-htpy)
      ( preserves-order-map-hom-Preorder P Q f)

  is-equiv-htpy-eq-hom-Preorder :
    (f g : hom-Preorder P Q) → is-equiv (htpy-eq-hom-Preorder f g)
  is-equiv-htpy-eq-hom-Preorder f =
    fundamental-theorem-id
      ( is-contr-total-htpy-hom-Preorder f)
      ( htpy-eq-hom-Preorder f)

  extensionality-hom-Preorder :
    (f g : hom-Preorder P Q) → Id f g ≃ htpy-hom-Preorder f g
  pr1 (extensionality-hom-Preorder f g) = htpy-eq-hom-Preorder f g
  pr2 (extensionality-hom-Preorder f g) = is-equiv-htpy-eq-hom-Preorder f g

  eq-htpy-hom-Preorder :
    (f g : hom-Preorder P Q) → htpy-hom-Preorder f g → Id f g
  eq-htpy-hom-Preorder f g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Preorder f g)
```

### The identity order preserving map

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  preserves-order-id-Preorder :
    preserves-order-Preorder P P (id {A = element-Preorder P})
  preserves-order-id-Preorder x y = id

  id-hom-Preorder : hom-Preorder P P
  pr1 id-hom-Preorder = id
  pr2 id-hom-Preorder = preserves-order-id-Preorder
```

### Composing order preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (P : Preorder l1 l2) (Q : Preorder l3 l4) (R : Preorder l5 l6)
  where

  preserves-order-comp-Preorder :
    (g : hom-Preorder Q R) (f : hom-Preorder P Q) →
    preserves-order-Preorder P R
      ( map-hom-Preorder Q R g ∘ map-hom-Preorder P Q f)
  preserves-order-comp-Preorder g f x y H =
    preserves-order-map-hom-Preorder Q R g
      ( map-hom-Preorder P Q f x)
      ( map-hom-Preorder P Q f y)
      ( preserves-order-map-hom-Preorder P Q f x y H)

  comp-hom-Preorder :
    (g : hom-Preorder Q R) (f : hom-Preorder P Q) → hom-Preorder P R
  pr1 (comp-hom-Preorder g f) =
     map-hom-Preorder Q R g ∘ map-hom-Preorder P Q f
  pr2 (comp-hom-Preorder g f) =
    preserves-order-comp-Preorder g f
```

### Unit laws for composition of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  left-unit-law-comp-hom-Preorder :
    (f : hom-Preorder P Q) →
    Id ( comp-hom-Preorder P Q Q (id-hom-Preorder Q) f) f
  left-unit-law-comp-hom-Preorder f =
    eq-htpy-hom-Preorder P Q
      ( comp-hom-Preorder P Q Q (id-hom-Preorder Q) f)
      ( f)
      ( refl-htpy)

  right-unit-law-comp-hom-Preorder :
    (f : hom-Preorder P Q) →
    Id (comp-hom-Preorder P P Q f (id-hom-Preorder P)) f
  right-unit-law-comp-hom-Preorder f =
    eq-htpy-hom-Preorder P Q
      ( comp-hom-Preorder P P Q f (id-hom-Preorder P))
      ( f)
      ( refl-htpy)
```

### Associativity of composition of order preserving maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (R : Preorder l5 l6) (S : Preorder l7 l8)
  (h : hom-Preorder R S) (g : hom-Preorder Q R) (f : hom-Preorder P Q)
  where

  associative-comp-hom-Preorder :
    Id ( comp-hom-Preorder P Q S (comp-hom-Preorder Q R S h g) f)
       ( comp-hom-Preorder P R S h (comp-hom-Preorder P Q R g f))
  associative-comp-hom-Preorder =
    eq-htpy-hom-Preorder P S
      ( comp-hom-Preorder P Q S (comp-hom-Preorder Q R S h g) f)
      ( comp-hom-Preorder P R S h (comp-hom-Preorder P Q R g f))
      ( refl-htpy)
```
