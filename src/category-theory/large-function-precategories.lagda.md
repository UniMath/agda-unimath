# Large function precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.large-function-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.dependent-products-of-large-precategories funext
open import category-theory.isomorphisms-in-large-precategories funext
open import category-theory.large-precategories funext

open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.sets funext
open import foundation.strictly-involutive-identity-types funext
open import foundation.universe-levels
```

</details>

## Idea

Given a type `I` and a
[large precategory](category-theory.large-precategories.md) `C`, the **large
function pre-category** `Cᴵ` consists of `I`-indexed families of objects of `C`
and `I`-indexed families of morphisms between them.

## Definition

### Large function precategories

```agda
module _
  {l1 : Level} {α : Level → Level} {β : Level → Level → Level}
  (I : UU l1) (C : Large-Precategory α β)
  where

  Large-Function-Precategory :
    Large-Precategory (λ l2 → l1 ⊔ α l2) (λ l2 l3 → l1 ⊔ β l2 l3)
  Large-Function-Precategory =
    Π-Large-Precategory I (λ _ → C)

  obj-Large-Function-Precategory : (l2 : Level) → UU (l1 ⊔ α l2)
  obj-Large-Function-Precategory =
    obj-Π-Large-Precategory I (λ _ → C)

  hom-set-Large-Function-Precategory :
    {l2 l3 : Level} →
    obj-Large-Function-Precategory l2 → obj-Large-Function-Precategory l3 →
    Set (l1 ⊔ β l2 l3)
  hom-set-Large-Function-Precategory =
    hom-set-Π-Large-Precategory I (λ _ → C)

  hom-Large-Function-Precategory :
    {l2 l3 : Level} →
    obj-Large-Function-Precategory l2 → obj-Large-Function-Precategory l3 →
    UU (l1 ⊔ β l2 l3)
  hom-Large-Function-Precategory =
    hom-Π-Large-Precategory I (λ _ → C)

  comp-hom-Large-Function-Precategory :
    {l2 l3 l4 : Level}
    {x : obj-Large-Function-Precategory l2}
    {y : obj-Large-Function-Precategory l3}
    {z : obj-Large-Function-Precategory l4} →
    hom-Large-Function-Precategory y z →
    hom-Large-Function-Precategory x y →
    hom-Large-Function-Precategory x z
  comp-hom-Large-Function-Precategory =
    comp-hom-Π-Large-Precategory I (λ _ → C)

  associative-comp-hom-Large-Function-Precategory :
    {l2 l3 l4 l5 : Level}
    {x : obj-Large-Function-Precategory l2}
    {y : obj-Large-Function-Precategory l3}
    {z : obj-Large-Function-Precategory l4}
    {w : obj-Large-Function-Precategory l5} →
    (h : hom-Large-Function-Precategory z w)
    (g : hom-Large-Function-Precategory y z)
    (f : hom-Large-Function-Precategory x y) →
    comp-hom-Large-Function-Precategory
      ( comp-hom-Large-Function-Precategory h g)
      ( f) ＝
    comp-hom-Large-Function-Precategory
      ( h)
      ( comp-hom-Large-Function-Precategory g f)
  associative-comp-hom-Large-Function-Precategory =
    associative-comp-hom-Π-Large-Precategory I (λ _ → C)

  involutive-eq-associative-comp-hom-Large-Function-Precategory :
    {l2 l3 l4 l5 : Level}
    {x : obj-Large-Function-Precategory l2}
    {y : obj-Large-Function-Precategory l3}
    {z : obj-Large-Function-Precategory l4}
    {w : obj-Large-Function-Precategory l5} →
    (h : hom-Large-Function-Precategory z w)
    (g : hom-Large-Function-Precategory y z)
    (f : hom-Large-Function-Precategory x y) →
    comp-hom-Large-Function-Precategory
      ( comp-hom-Large-Function-Precategory h g)
      ( f) ＝ⁱ
    comp-hom-Large-Function-Precategory
      ( h)
      ( comp-hom-Large-Function-Precategory g f)
  involutive-eq-associative-comp-hom-Large-Function-Precategory =
    involutive-eq-associative-comp-hom-Π-Large-Precategory I (λ _ → C)

  id-hom-Large-Function-Precategory :
    {l2 : Level} {x : obj-Large-Function-Precategory l2} →
    hom-Large-Function-Precategory x x
  id-hom-Large-Function-Precategory =
    id-hom-Π-Large-Precategory I (λ _ → C)

  left-unit-law-comp-hom-Large-Function-Precategory :
    {l2 l3 : Level}
    {x : obj-Large-Function-Precategory l2}
    {y : obj-Large-Function-Precategory l3}
    (f : hom-Large-Function-Precategory x y) →
    comp-hom-Large-Function-Precategory id-hom-Large-Function-Precategory f ＝ f
  left-unit-law-comp-hom-Large-Function-Precategory =
    left-unit-law-comp-hom-Π-Large-Precategory I (λ _ → C)

  right-unit-law-comp-hom-Large-Function-Precategory :
    {l2 l3 : Level}
    {x : obj-Large-Function-Precategory l2}
    {y : obj-Large-Function-Precategory l3}
    (f : hom-Large-Function-Precategory x y) →
    comp-hom-Large-Function-Precategory f id-hom-Large-Function-Precategory ＝ f
  right-unit-law-comp-hom-Large-Function-Precategory =
    right-unit-law-comp-hom-Π-Large-Precategory I (λ _ → C)
```

## Properties

### Isomorphisms in the dependent product precategory are fiberwise isomorphisms

```agda
module _
  {l1 l2 l3 : Level} {α : Level → Level} {β : Level → Level → Level}
  (I : UU l1) (C : Large-Precategory α β)
  {x : obj-Large-Function-Precategory I C l2}
  {y : obj-Large-Function-Precategory I C l3}
  where

  is-fiberwise-iso-is-iso-Large-Function-Precategory :
    (f : hom-Large-Function-Precategory I C x y) →
    is-iso-Large-Precategory (Large-Function-Precategory I C) f →
    (i : I) → is-iso-Large-Precategory C (f i)
  is-fiberwise-iso-is-iso-Large-Function-Precategory =
    is-fiberwise-iso-is-iso-Π-Large-Precategory I (λ _ → C)

  fiberwise-iso-iso-Large-Function-Precategory :
    iso-Large-Precategory (Large-Function-Precategory I C) x y →
    (i : I) → iso-Large-Precategory C (x i) (y i)
  fiberwise-iso-iso-Large-Function-Precategory =
    fiberwise-iso-iso-Π-Large-Precategory I (λ _ → C)

  is-iso-is-fiberwise-iso-Large-Function-Precategory :
    (f : hom-Large-Function-Precategory I C x y) →
    ((i : I) → is-iso-Large-Precategory C (f i)) →
    is-iso-Large-Precategory (Large-Function-Precategory I C) f
  is-iso-is-fiberwise-iso-Large-Function-Precategory =
    is-iso-is-fiberwise-iso-Π-Large-Precategory I (λ _ → C)

  iso-fiberwise-iso-Large-Function-Precategory :
    ((i : I) → iso-Large-Precategory C (x i) (y i)) →
    iso-Large-Precategory (Large-Function-Precategory I C) x y
  iso-fiberwise-iso-Large-Function-Precategory =
    iso-fiberwise-iso-Π-Large-Precategory I (λ _ → C)

  is-equiv-is-fiberwise-iso-is-iso-Large-Function-Precategory :
    (f : hom-Large-Function-Precategory I C x y) →
    is-equiv (is-fiberwise-iso-is-iso-Large-Function-Precategory f)
  is-equiv-is-fiberwise-iso-is-iso-Large-Function-Precategory =
    is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategory I (λ _ → C)

  equiv-is-fiberwise-iso-is-iso-Large-Function-Precategory :
    (f : hom-Large-Function-Precategory I C x y) →
    ( is-iso-Large-Precategory (Large-Function-Precategory I C) f) ≃
    ( (i : I) → is-iso-Large-Precategory C (f i))
  equiv-is-fiberwise-iso-is-iso-Large-Function-Precategory =
    equiv-is-fiberwise-iso-is-iso-Π-Large-Precategory I (λ _ → C)

  is-equiv-is-iso-is-fiberwise-iso-Large-Function-Precategory :
    (f : hom-Large-Function-Precategory I C x y) →
    is-equiv (is-iso-is-fiberwise-iso-Large-Function-Precategory f)
  is-equiv-is-iso-is-fiberwise-iso-Large-Function-Precategory =
    is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategory I (λ _ → C)

  equiv-is-iso-is-fiberwise-iso-Large-Function-Precategory :
    ( f : hom-Large-Function-Precategory I C x y) →
    ( (i : I) → is-iso-Large-Precategory C (f i)) ≃
    ( is-iso-Large-Precategory (Large-Function-Precategory I C) f)
  equiv-is-iso-is-fiberwise-iso-Large-Function-Precategory =
    equiv-is-iso-is-fiberwise-iso-Π-Large-Precategory I (λ _ → C)

  is-equiv-fiberwise-iso-iso-Large-Function-Precategory :
    is-equiv fiberwise-iso-iso-Large-Function-Precategory
  is-equiv-fiberwise-iso-iso-Large-Function-Precategory =
    is-equiv-fiberwise-iso-iso-Π-Large-Precategory I (λ _ → C)

  equiv-fiberwise-iso-iso-Large-Function-Precategory :
    ( iso-Large-Precategory (Large-Function-Precategory I C) x y) ≃
    ( (i : I) → iso-Large-Precategory C (x i) (y i))
  equiv-fiberwise-iso-iso-Large-Function-Precategory =
    equiv-fiberwise-iso-iso-Π-Large-Precategory I (λ _ → C)

  is-equiv-iso-fiberwise-iso-Large-Function-Precategory :
    is-equiv iso-fiberwise-iso-Large-Function-Precategory
  is-equiv-iso-fiberwise-iso-Large-Function-Precategory =
    is-equiv-iso-fiberwise-iso-Π-Large-Precategory I (λ _ → C)

  equiv-iso-fiberwise-iso-Large-Function-Precategory :
    ( (i : I) → iso-Large-Precategory C (x i) (y i)) ≃
    ( iso-Large-Precategory (Large-Function-Precategory I C) x y)
  equiv-iso-fiberwise-iso-Large-Function-Precategory =
    equiv-iso-fiberwise-iso-Π-Large-Precategory I (λ _ → C)
```
