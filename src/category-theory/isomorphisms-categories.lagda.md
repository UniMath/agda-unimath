# Isomorphisms in categories

```agda
module category-theory.isomorphisms-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universe-levels
```

</details>

## Idea

An isomorphism in a category is an isomorphism in the underlying precategory.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  is-iso-Cat : {x y : obj-Cat C} (f : type-hom-Cat C x y) → UU l2
  is-iso-Cat = is-iso-Precat (precat-Cat C)

  iso-Cat : (x y : obj-Cat C) → UU l2
  iso-Cat = iso-Precat (precat-Cat C)

  hom-iso-Cat : {x y : obj-Cat C} → iso-Cat x y → type-hom-Cat C x y
  hom-iso-Cat f = pr1 f

  is-iso-hom-iso-Cat :
    {x y : obj-Cat C} (f : iso-Cat x y) → is-iso-Cat (hom-iso-Cat f)
  is-iso-hom-iso-Cat f = pr2 f

  hom-inv-iso-Cat : {x y : obj-Cat C} → iso-Cat x y → type-hom-Cat C y x
  hom-inv-iso-Cat f = pr1 (is-iso-hom-iso-Cat f)

  issec-hom-inv-iso-Cat :
    {x y : obj-Cat C} (f : iso-Cat x y) →
    comp-hom-Cat C (hom-iso-Cat f) (hom-inv-iso-Cat f) ＝ id-hom-Cat C
  issec-hom-inv-iso-Cat f = pr1 (pr2 (is-iso-hom-iso-Cat f))

  isretr-hom-inv-iso-Cat :
    {x y : obj-Cat C} (f : iso-Cat x y) →
    comp-hom-Cat C (hom-inv-iso-Cat f) (hom-iso-Cat f) ＝ id-hom-Cat C
  isretr-hom-inv-iso-Cat f = pr2 (pr2 (is-iso-hom-iso-Cat f))

  inv-iso-Cat : {x y : obj-Cat C} → iso-Cat x y → iso-Cat y x
  inv-iso-Cat f =
    pair
      ( hom-inv-iso-Cat f)
      ( pair
        ( hom-iso-Cat f)
        ( pair
          ( isretr-hom-inv-iso-Cat f)
          ( issec-hom-inv-iso-Cat f)))
```

### Precomposing by isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  precomp-iso-Cat :
    {x y z : obj-Cat C} →
    iso-Cat C x y → type-hom-Cat C y z → type-hom-Cat C x z
  precomp-iso-Cat f g = comp-hom-Cat C g (hom-iso-Cat C f)
```

### Postcomposing by isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  postcomp-iso-Cat :
    {x y z : obj-Cat C} →
    iso-Cat C y z → type-hom-Cat C x y → type-hom-Cat C x z
  postcomp-iso-Cat f g = comp-hom-Cat C (hom-iso-Cat C f) g
```

## Examples

### The identity morphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  is-iso-id-hom-Cat : {x : obj-Cat C} → is-iso-Cat C (id-hom-Cat C {x})
  is-iso-id-hom-Cat = is-iso-id-hom-Precat (precat-Cat C)

  id-iso-Cat : {x : obj-Cat C} → iso-Cat C x x
  id-iso-Cat = id-iso-Precat (precat-Cat C)
```

### Compositions of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  hom-comp-iso-Cat :
    {x y z : obj-Cat C} → iso-Cat C y z → iso-Cat C x y → type-hom-Cat C x z
  hom-comp-iso-Cat g f = comp-hom-Cat C (hom-iso-Cat C g) (hom-iso-Cat C f)

  hom-inv-comp-iso-Cat :
    {x y z : obj-Cat C} → iso-Cat C y z → iso-Cat C x y → type-hom-Cat C z x
  hom-inv-comp-iso-Cat g f =
    comp-hom-Cat C (hom-inv-iso-Cat C f) (hom-inv-iso-Cat C g)

  issec-hom-inv-comp-iso-Cat :
    {x y z : obj-Cat C} (g : iso-Cat C y z) (f : iso-Cat C x y) →
    comp-hom-Cat C (hom-comp-iso-Cat g f) (hom-inv-comp-iso-Cat g f)
    ＝ id-hom-Cat C
  issec-hom-inv-comp-iso-Cat g f =
    equational-reasoning
      comp-hom-Cat C (hom-comp-iso-Cat g f) (hom-inv-comp-iso-Cat g f)
      ＝ comp-hom-Cat C
          ( hom-iso-Cat C g)
          ( comp-hom-Cat C
            ( hom-iso-Cat C f)
            ( hom-inv-comp-iso-Cat g f))
        by
        assoc-comp-hom-Cat C
          ( hom-iso-Cat C g)
          ( hom-iso-Cat C f)
          ( hom-inv-comp-iso-Cat g f)
      ＝ comp-hom-Cat C
          ( hom-iso-Cat C g)
          ( comp-hom-Cat C
            ( comp-hom-Cat C
              ( hom-iso-Cat C f)
              ( hom-inv-iso-Cat C f))
            ( hom-inv-iso-Cat C g))
        by
        ap
          ( comp-hom-Cat C (hom-iso-Cat C g))
          ( inv
            ( assoc-comp-hom-Cat C
              ( hom-iso-Cat C f)
              ( hom-inv-iso-Cat C f)
              ( hom-inv-iso-Cat C g)))
      ＝ comp-hom-Cat C
          ( hom-iso-Cat C g)
          ( comp-hom-Cat C
            ( id-hom-Cat C)
            ( hom-inv-iso-Cat C g))
        by
        ap
          ( comp-hom-Cat C (hom-iso-Cat C g))
          ( ap
            ( λ h → comp-hom-Cat C h (hom-inv-iso-Cat C g))
            ( issec-hom-inv-iso-Cat C f))
      ＝ comp-hom-Cat C (hom-iso-Cat C g) (hom-inv-iso-Cat C g)
        by
        ap
          ( comp-hom-Cat C (hom-iso-Cat C g))
          ( left-unit-law-comp-hom-Cat C (hom-inv-iso-Cat C g))
      ＝ id-hom-Cat C
        by
        issec-hom-inv-iso-Cat C g

  isretr-hom-inv-comp-iso-Cat :
    {x y z : obj-Cat C} (g : iso-Cat C y z) (f : iso-Cat C x y) →
    ( comp-hom-Cat C (hom-inv-comp-iso-Cat g f) (hom-comp-iso-Cat g f)) ＝
    ( id-hom-Cat C)
  isretr-hom-inv-comp-iso-Cat g f =
    equational-reasoning
      comp-hom-Cat C (hom-inv-comp-iso-Cat g f) (hom-comp-iso-Cat g f)
      ＝ comp-hom-Cat C
          ( hom-inv-iso-Cat C f)
          ( comp-hom-Cat C
            ( hom-inv-iso-Cat C g)
            ( hom-comp-iso-Cat g f))
        by
        assoc-comp-hom-Cat C
          ( hom-inv-iso-Cat C f)
          ( hom-inv-iso-Cat C g)
          ( hom-comp-iso-Cat g f)
      ＝ comp-hom-Cat C
          ( hom-inv-iso-Cat C f)
          ( comp-hom-Cat C
            ( comp-hom-Cat C
              ( hom-inv-iso-Cat C g)
              ( hom-iso-Cat C g))
            ( hom-iso-Cat C f))
        by
        ap
          ( comp-hom-Cat C (hom-inv-iso-Cat C f))
          ( inv
            ( assoc-comp-hom-Cat C
              ( hom-inv-iso-Cat C g)
              ( hom-iso-Cat C g)
              ( hom-iso-Cat C f)))
      ＝ comp-hom-Cat C
          ( hom-inv-iso-Cat C f)
          ( comp-hom-Cat C
            ( id-hom-Cat C)
            ( hom-iso-Cat C f))
        by
        ap
          ( comp-hom-Cat C (hom-inv-iso-Cat C f))
          ( ap
            ( λ h → comp-hom-Cat C h (hom-iso-Cat C f))
            ( isretr-hom-inv-iso-Cat C g))
      ＝ comp-hom-Cat C (hom-inv-iso-Cat C f) (hom-iso-Cat C f)
        by
        ap
          ( comp-hom-Cat C (hom-inv-iso-Cat C f))
          ( left-unit-law-comp-hom-Cat C (hom-iso-Cat C f))
      ＝ id-hom-Cat C
        by
        isretr-hom-inv-iso-Cat C f

  is-iso-hom-comp-iso-Cat :
    {x y z : obj-Cat C} (g : iso-Cat C y z) (f : iso-Cat C x y) →
    is-iso-Cat C (hom-comp-iso-Cat g f)
  pr1 (is-iso-hom-comp-iso-Cat g f) =
    hom-inv-comp-iso-Cat g f
  pr1 (pr2 (is-iso-hom-comp-iso-Cat g f)) =
    issec-hom-inv-comp-iso-Cat g f
  pr2 (pr2 (is-iso-hom-comp-iso-Cat g f)) =
    isretr-hom-inv-comp-iso-Cat g f

  comp-iso-Cat :
    {x y z : obj-Cat C} → iso-Cat C y z → iso-Cat C x y → iso-Cat C x z
  pr1 (comp-iso-Cat g f) = hom-comp-iso-Cat g f
  pr2 (comp-iso-Cat g f) = is-iso-hom-comp-iso-Cat g f
```

## Properties

### The property of being an isomorphism is a proposition

```agda
is-prop-is-iso-Cat :
  {l1 l2 : Level} (C : Cat l1 l2) →
  {x y : obj-Cat C} (f : type-hom-Cat C x y) → is-prop (is-iso-Cat C f)
is-prop-is-iso-Cat C = is-prop-is-iso-Precat (precat-Cat C)
```

### Characterizing equality of isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2) {x y : obj-Cat C} (f : iso-Cat C x y)
  where

  Eq-iso-Cat : iso-Cat C x y → UU l2
  Eq-iso-Cat g = hom-iso-Cat C f ＝ hom-iso-Cat C g

  refl-Eq-iso-Cat : Eq-iso-Cat f
  refl-Eq-iso-Cat = refl

  is-contr-total-Eq-iso-Cat :
    is-contr (Σ (iso-Cat C x y) Eq-iso-Cat)
  is-contr-total-Eq-iso-Cat =
    is-contr-total-Eq-subtype
      ( is-contr-total-path (hom-iso-Cat C f))
      ( is-prop-is-iso-Cat C)
      ( hom-iso-Cat C f)
      ( refl)
      ( is-iso-hom-iso-Cat C f)

  Eq-eq-iso-Cat :
    (g : iso-Cat C x y) → (f ＝ g) → Eq-iso-Cat g
  Eq-eq-iso-Cat .f refl = refl-Eq-iso-Cat

  is-equiv-Eq-eq-iso-Cat :
    (g : iso-Cat C x y) → is-equiv (Eq-eq-iso-Cat g)
  is-equiv-Eq-eq-iso-Cat =
    fundamental-theorem-id
      is-contr-total-Eq-iso-Cat
      Eq-eq-iso-Cat

  extensionality-iso-Cat :
    (g : iso-Cat C x y) → (f ＝ g) ≃ Eq-iso-Cat g
  pr1 (extensionality-iso-Cat g) = Eq-eq-iso-Cat g
  pr2 (extensionality-iso-Cat g) = is-equiv-Eq-eq-iso-Cat g

  eq-Eq-iso-Cat :
    (g : iso-Cat C x y) → Eq-iso-Cat g → (f ＝ g)
  eq-Eq-iso-Cat g = map-inv-equiv (extensionality-iso-Cat g)
```

### Groupoid laws for composition of isomorphisms in a category

#### Left unit law

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  left-unit-law-comp-iso-Cat :
    {x y : obj-Cat C} (f : iso-Cat C x y) →
    comp-iso-Cat C (id-iso-Cat C) f ＝ f
  left-unit-law-comp-iso-Cat f =
    eq-Eq-iso-Cat C
      (comp-iso-Cat C (id-iso-Cat C) f)
      ( f)
      ( left-unit-law-comp-hom-Cat C (hom-iso-Cat C f))
```

#### Right unit law

```agda
  right-unit-law-comp-iso-Cat :
    {x y : obj-Cat C} (f : iso-Cat C x y) →
    comp-iso-Cat C f (id-iso-Cat C) ＝ f
  right-unit-law-comp-iso-Cat f =
    eq-Eq-iso-Cat C
      ( comp-iso-Cat C f (id-iso-Cat C))
      ( f)
      ( right-unit-law-comp-hom-Cat C (hom-iso-Cat C f))
```

#### Associatitivity
```agda
  assoc-comp-iso-Cat :
    {x y z w : obj-Cat C}
    (h : iso-Cat C z w) (g : iso-Cat C y z) (f : iso-Cat C x y) →
    comp-iso-Cat C (comp-iso-Cat C h g) f ＝ comp-iso-Cat C h (comp-iso-Cat C g f)
  assoc-comp-iso-Cat h g f =
    eq-Eq-iso-Cat C
      ( comp-iso-Cat C (comp-iso-Cat C h g) f)
      ( comp-iso-Cat C h (comp-iso-Cat C g f))
      ( assoc-comp-hom-Cat C
        ( hom-iso-Cat C h)
        ( hom-iso-Cat C g)
        ( hom-iso-Cat C f))
```

#### Left inverse law

```agda
  left-inverse-law-comp-iso-Cat : {x y : obj-Cat C} (f : iso-Cat C x y) →
    comp-iso-Cat C (inv-iso-Cat C f) f ＝ id-iso-Cat C
  left-inverse-law-comp-iso-Cat f =
    eq-Eq-iso-Cat C
      ( comp-iso-Cat C (inv-iso-Cat C f) f)
      ( id-iso-Cat C)
      ( isretr-hom-inv-iso-Cat C f)
```

#### Right inverse law

```agda
  right-inverse-law-comp-iso-Cat : {x y : obj-Cat C} (f : iso-Cat C x y) →
    comp-iso-Cat C f (inv-iso-Cat C f) ＝ id-iso-Cat C
  right-inverse-law-comp-iso-Cat f =
    eq-Eq-iso-Cat C
      ( comp-iso-Cat C f (inv-iso-Cat C f))
      ( id-iso-Cat C)
      ( issec-hom-inv-iso-Cat C f)
```

### Equalities give rise to isomorphisms

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  iso-eq-Cat : {x y : obj-Cat C} → x ＝ y → iso-Cat C x y
  iso-eq-Cat {x} {y} = iso-eq-Precat (precat-Cat C) x y

  preserves-concat-iso-eq-Cat :
    {x y z : obj-Cat C} (p : x ＝ y) (q : y ＝ z) →
    iso-eq-Cat (p ∙ q) ＝
    comp-iso-Cat C (iso-eq-Cat q) (iso-eq-Cat p)
  preserves-concat-iso-eq-Cat refl q =
    inv (right-unit-law-comp-iso-Cat C (iso-eq-Cat q))
```

## Properties

### Extensionality of the type of objects in a category

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  extensionality-obj-Cat :
    (x y : obj-Cat C) → (x ＝ y) ≃ iso-Cat C x y
  pr1 (extensionality-obj-Cat x y) = iso-eq-Cat C
  pr2 (extensionality-obj-Cat x y) = is-category-Cat C x y

  eq-iso-Cat :
    {x y : obj-Cat C} → iso-Cat C x y → x ＝ y
  eq-iso-Cat {x} {y} = map-inv-equiv (extensionality-obj-Cat x y)

  issec-eq-iso-Cat :
    {x y : obj-Cat C} (f : iso-Cat C x y) →
    iso-eq-Cat C (eq-iso-Cat f) ＝ f
  issec-eq-iso-Cat {x} {y} = issec-map-inv-equiv (extensionality-obj-Cat x y)

  isretr-eq-iso-Cat :
    {x y : obj-Cat C} (p : x ＝ y) → eq-iso-Cat (iso-eq-Cat C p) ＝ p
  isretr-eq-iso-Cat {x} {y} = isretr-map-inv-equiv (extensionality-obj-Cat x y)

  preserves-comp-eq-iso-Cat :
    {x y z : obj-Cat C} (g : iso-Cat C y z) (f : iso-Cat C x y) →
    eq-iso-Cat (comp-iso-Cat C g f) ＝ (eq-iso-Cat f ∙ eq-iso-Cat g)
  preserves-comp-eq-iso-Cat g f =
    equational-reasoning
      eq-iso-Cat (comp-iso-Cat C g f)
      ＝ eq-iso-Cat
          ( comp-iso-Cat C
            ( iso-eq-Cat C (eq-iso-Cat g))
            ( iso-eq-Cat C (eq-iso-Cat f)))
        by
        ap eq-iso-Cat
          ( ap-binary
            ( comp-iso-Cat C)
            ( inv (issec-eq-iso-Cat g))
            ( inv (issec-eq-iso-Cat f)))
      ＝ eq-iso-Cat (iso-eq-Cat C (eq-iso-Cat f ∙ eq-iso-Cat g))
        by
        ap eq-iso-Cat
          ( inv
            ( preserves-concat-iso-eq-Cat C
              ( eq-iso-Cat f)
              ( eq-iso-Cat g)))
      ＝ eq-iso-Cat f ∙ eq-iso-Cat g
        by
        isretr-eq-iso-Cat (eq-iso-Cat f ∙ eq-iso-Cat g)
```

### The type of isomorphisms forms a set

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2)
  where

  is-set-iso-Cat : (x y : obj-Cat C) → is-set (iso-Cat C x y)
  is-set-iso-Cat = is-set-iso-Precat (precat-Cat C)

  iso-Cat-Set : (x y : obj-Cat C) → Set l2
  iso-Cat-Set = iso-Precat-Set (precat-Cat C)
```

### A morphism is an isomorphism if and only if precomposing by it is an equivalence

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2) {x y : obj-Cat C} (f : type-hom-Cat C x y)
  where

{-
  is-equiv-precomp-is-iso-hom-Cat :
    (H : is-iso-Cat C f) →
    (z : obj-Cat C) → is-equiv (precomp-iso-Cat C {z = z} (pair f H))
  is-equiv-precomp-is-iso-hom-Cat H z = {!!}
  -}
```
