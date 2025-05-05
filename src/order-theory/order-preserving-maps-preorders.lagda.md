# Order preserving maps between preorders

```agda
module order-theory.order-preserving-maps-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.strictly-involutive-identity-types
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.torsorial-type-families

open import order-theory.preorders
```

</details>

## Idea

A map `f : P → Q` between the underlying types of two
[preorders](order-theory.preorders.md) is said to be an
{{#concept "order preserving map" Disambiguation="preorder" Agda=hom-Preorder}}
if for any two elements `x ≤ y` in `P` we have `f x ≤ f y` in `Q`.

## Definition

### The predicate of being an order preserving map

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (f : type-Preorder P → type-Preorder Q)
  where

  preserves-order-prop-Preorder :
    Prop (l1 ⊔ l2 ⊔ l4)
  preserves-order-prop-Preorder =
    Π-Prop
      ( type-Preorder P)
      ( λ x →
        Π-Prop
          ( type-Preorder P)
          ( λ y →
            hom-Prop
              ( leq-prop-Preorder P x y)
              ( leq-prop-Preorder Q (f x) (f y))))

  preserves-order-Preorder :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-order-Preorder =
    type-Prop preserves-order-prop-Preorder

  is-prop-preserves-order-Preorder :
    is-prop preserves-order-Preorder
  is-prop-preserves-order-Preorder =
    is-prop-type-Prop preserves-order-prop-Preorder
```

### The type of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  hom-Preorder :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Preorder =
    Σ (type-Preorder P → type-Preorder Q) (preserves-order-Preorder P Q)

  map-hom-Preorder :
    hom-Preorder → type-Preorder P → type-Preorder Q
  map-hom-Preorder =
    pr1

  preserves-order-hom-Preorder :
    (f : hom-Preorder) → preserves-order-Preorder P Q (map-hom-Preorder f)
  preserves-order-hom-Preorder =
    pr2
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

  is-torsorial-htpy-hom-Preorder :
    (f : hom-Preorder P Q) → is-torsorial (htpy-hom-Preorder f)
  is-torsorial-htpy-hom-Preorder f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-hom-Preorder P Q f))
      ( is-prop-preserves-order-Preorder P Q)
      ( map-hom-Preorder P Q f)
      ( refl-htpy)
      ( preserves-order-hom-Preorder P Q f)

  is-equiv-htpy-eq-hom-Preorder :
    (f g : hom-Preorder P Q) → is-equiv (htpy-eq-hom-Preorder f g)
  is-equiv-htpy-eq-hom-Preorder f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-Preorder f)
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
    preserves-order-Preorder P P (id {A = type-Preorder P})
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
    preserves-order-hom-Preorder Q R g
      ( map-hom-Preorder P Q f x)
      ( map-hom-Preorder P Q f y)
      ( preserves-order-hom-Preorder P Q f x y H)

  comp-hom-Preorder :
    (g : hom-Preorder Q R) (f : hom-Preorder P Q) →
    hom-Preorder P R
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
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (P : Preorder l1 l2) (Q : Preorder l3 l4)
  (R : Preorder l5 l6) (S : Preorder l7 l8)
  (h : hom-Preorder R S)
  (g : hom-Preorder Q R)
  (f : hom-Preorder P Q)
  where

  associative-comp-hom-Preorder :
    comp-hom-Preorder P Q S (comp-hom-Preorder Q R S h g) f ＝
    comp-hom-Preorder P R S h (comp-hom-Preorder P Q R g f)
  associative-comp-hom-Preorder =
    eq-htpy-hom-Preorder P S
      ( comp-hom-Preorder P Q S (comp-hom-Preorder Q R S h g) f)
      ( comp-hom-Preorder P R S h (comp-hom-Preorder P Q R g f))
      ( refl-htpy)

  involutive-eq-associative-comp-hom-Preorder :
    comp-hom-Preorder P Q S (comp-hom-Preorder Q R S h g) f ＝ⁱ
    comp-hom-Preorder P R S h (comp-hom-Preorder P Q R g f)
  involutive-eq-associative-comp-hom-Preorder =
    involutive-eq-eq associative-comp-hom-Preorder
```

### Pointwise inequality of order preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Preorder l1 l2) (Q : Preorder l3 l4)
  where

  leq-hom-Preorder : (f g : hom-Preorder P Q) → UU (l1 ⊔ l4)
  leq-hom-Preorder f g =
    (x : type-Preorder P) →
    leq-Preorder Q (map-hom-Preorder P Q f x) (map-hom-Preorder P Q g x)

  is-prop-leq-hom-Preorder :
    (f g : hom-Preorder P Q) → is-prop (leq-hom-Preorder f g)
  is-prop-leq-hom-Preorder f g =
    is-prop-Π (λ x → is-prop-leq-Preorder Q _ _)

  leq-prop-hom-Preorder :
    (f g : hom-Preorder P Q) → Prop (l1 ⊔ l4)
  pr1 (leq-prop-hom-Preorder f g) = leq-hom-Preorder f g
  pr2 (leq-prop-hom-Preorder f g) = is-prop-leq-hom-Preorder f g

  refl-leq-hom-Preorder : (f : hom-Preorder P Q) → leq-hom-Preorder f f
  refl-leq-hom-Preorder f x = refl-leq-Preorder Q (map-hom-Preorder P Q f x)

  transitive-leq-hom-Preorder :
    (f g h : hom-Preorder P Q) →
    leq-hom-Preorder g h → leq-hom-Preorder f g → leq-hom-Preorder f h
  transitive-leq-hom-Preorder f g h H K x =
    transitive-leq-Preorder Q _ _ _ (H x) (K x)

  hom-preorder-Preorder : Preorder (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l4)
  pr1 hom-preorder-Preorder = hom-Preorder P Q
  pr1 (pr2 hom-preorder-Preorder) = leq-prop-hom-Preorder
  pr1 (pr2 (pr2 hom-preorder-Preorder)) = refl-leq-hom-Preorder
  pr2 (pr2 (pr2 hom-preorder-Preorder)) = transitive-leq-hom-Preorder
```
