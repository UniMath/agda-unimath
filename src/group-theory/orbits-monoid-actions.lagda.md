# The precategory of orbits of a monoid action

```agda
module group-theory.orbits-monoid-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import group-theory.monoid-actions
open import group-theory.monoids
```

</details>

## Idea

Given a monoid action `M → endo-Monoid X` we can define a category in which the objects are the elements of the set `X` and a morphism from `x` to `y` is an element `m` of the monoid `M` such that `mx = y`.

## Definition

### The precategory of orbits of a monoid action

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (X : Monoid-Action l2 M)
  where

  hom-orbit-Monoid-Action : (x y : type-Monoid-Action M X) → UU (l1 ⊔ l2)
  hom-orbit-Monoid-Action x y =
    Σ (type-Monoid M) ( λ m → Id (mul-Monoid-Action M X m x) y)

  element-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} → hom-orbit-Monoid-Action x y → type-Monoid M
  element-hom-orbit-Monoid-Action f = pr1 f

  eq-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f : hom-orbit-Monoid-Action x y) →
    Id (mul-Monoid-Action M X (element-hom-orbit-Monoid-Action f) x) y
  eq-hom-orbit-Monoid-Action f = pr2 f

  htpy-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f g : hom-orbit-Monoid-Action x y) →
    UU l1
  htpy-hom-orbit-Monoid-Action {x} {y} f g =
    Id ( element-hom-orbit-Monoid-Action f)
       ( element-hom-orbit-Monoid-Action g)

  refl-htpy-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f : hom-orbit-Monoid-Action x y) →
    htpy-hom-orbit-Monoid-Action f f
  refl-htpy-hom-orbit-Monoid-Action f = refl

  htpy-eq-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f g : hom-orbit-Monoid-Action x y) →
    Id f g → htpy-hom-orbit-Monoid-Action f g
  htpy-eq-hom-orbit-Monoid-Action f .f refl =
    refl-htpy-hom-orbit-Monoid-Action f

  is-contr-total-htpy-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f : hom-orbit-Monoid-Action x y) →
    is-contr (Σ (hom-orbit-Monoid-Action x y) (htpy-hom-orbit-Monoid-Action f))
  is-contr-total-htpy-hom-orbit-Monoid-Action {x} {y} f =
    is-contr-total-Eq-subtype
      ( is-contr-total-path (element-hom-orbit-Monoid-Action f))
      ( λ u →
        is-set-type-Monoid-Action M X (mul-Monoid-Action M X u x) y)
      ( element-hom-orbit-Monoid-Action f)
      ( refl)
      ( eq-hom-orbit-Monoid-Action f)

  is-equiv-htpy-eq-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f g : hom-orbit-Monoid-Action x y) →
    is-equiv (htpy-eq-hom-orbit-Monoid-Action f g)
  is-equiv-htpy-eq-hom-orbit-Monoid-Action f =
    fundamental-theorem-id
      ( is-contr-total-htpy-hom-orbit-Monoid-Action f)
      ( htpy-eq-hom-orbit-Monoid-Action f)

  extensionality-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f g : hom-orbit-Monoid-Action x y) →
    Id f g ≃ htpy-hom-orbit-Monoid-Action f g
  pr1 (extensionality-hom-orbit-Monoid-Action f g) =
    htpy-eq-hom-orbit-Monoid-Action f g
  pr2 (extensionality-hom-orbit-Monoid-Action f g) =
    is-equiv-htpy-eq-hom-orbit-Monoid-Action f g

  eq-htpy-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} {f g : hom-orbit-Monoid-Action x y} →
    htpy-hom-orbit-Monoid-Action f g → Id f g
  eq-htpy-hom-orbit-Monoid-Action {x} {y} {f} {g} =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-orbit-Monoid-Action f g)

  is-prop-htpy-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f g : hom-orbit-Monoid-Action x y) →
    is-prop (htpy-hom-orbit-Monoid-Action f g)
  is-prop-htpy-hom-orbit-Monoid-Action f g =
    is-set-type-Monoid M
      ( element-hom-orbit-Monoid-Action f)
      ( element-hom-orbit-Monoid-Action g)

  is-set-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} →
    is-set (hom-orbit-Monoid-Action x y)
  is-set-hom-orbit-Monoid-Action {x} {y} f g =
    is-prop-equiv
      ( extensionality-hom-orbit-Monoid-Action f g)
      ( is-prop-htpy-hom-orbit-Monoid-Action f g)

  hom-orbit-monoid-action-Set :
    (x y : type-Monoid-Action M X) → Set (l1 ⊔ l2)
  pr1 (hom-orbit-monoid-action-Set x y) = hom-orbit-Monoid-Action x y
  pr2 (hom-orbit-monoid-action-Set x y) = is-set-hom-orbit-Monoid-Action

  id-hom-orbit-Monoid-Action :
    (x : type-Monoid-Action M X) → hom-orbit-Monoid-Action x x
  pr1 (id-hom-orbit-Monoid-Action x) = unit-Monoid M
  pr2 (id-hom-orbit-Monoid-Action x) = unit-law-mul-Monoid-Action M X x

  comp-hom-orbit-Monoid-Action :
    {x y z : type-Monoid-Action M X} →
    hom-orbit-Monoid-Action y z → hom-orbit-Monoid-Action x y →
    hom-orbit-Monoid-Action x z
  pr1 (comp-hom-orbit-Monoid-Action g f) =
    mul-Monoid M
      ( element-hom-orbit-Monoid-Action g)
      ( element-hom-orbit-Monoid-Action f)
  pr2 (comp-hom-orbit-Monoid-Action {x} g f) =
    ( associative-mul-Monoid-Action M X
      ( element-hom-orbit-Monoid-Action g)
      ( element-hom-orbit-Monoid-Action f)
      ( x)) ∙
    ( ( ap-mul-Monoid-Action M X (eq-hom-orbit-Monoid-Action f)) ∙
      ( eq-hom-orbit-Monoid-Action g))

  associative-comp-hom-orbit-Monoid-Action :
    {x y z w : type-Monoid-Action M X} (h : hom-orbit-Monoid-Action z w)
    (g : hom-orbit-Monoid-Action y z) (f : hom-orbit-Monoid-Action x y) →
    Id ( comp-hom-orbit-Monoid-Action (comp-hom-orbit-Monoid-Action h g) f)
       ( comp-hom-orbit-Monoid-Action h (comp-hom-orbit-Monoid-Action g f))
  associative-comp-hom-orbit-Monoid-Action h g f =
    eq-htpy-hom-orbit-Monoid-Action
      ( associative-mul-Monoid M
        ( element-hom-orbit-Monoid-Action h)
        ( element-hom-orbit-Monoid-Action g)
        ( element-hom-orbit-Monoid-Action f))

  left-unit-law-comp-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f : hom-orbit-Monoid-Action x y) →
    Id (comp-hom-orbit-Monoid-Action (id-hom-orbit-Monoid-Action y) f) f
  left-unit-law-comp-hom-orbit-Monoid-Action f =
    eq-htpy-hom-orbit-Monoid-Action
      ( left-unit-law-mul-Monoid M (element-hom-orbit-Monoid-Action f))

  right-unit-law-comp-hom-orbit-Monoid-Action :
    {x y : type-Monoid-Action M X} (f : hom-orbit-Monoid-Action x y) →
    Id (comp-hom-orbit-Monoid-Action f (id-hom-orbit-Monoid-Action x)) f
  right-unit-law-comp-hom-orbit-Monoid-Action f =
    eq-htpy-hom-orbit-Monoid-Action
      ( right-unit-law-mul-Monoid M (element-hom-orbit-Monoid-Action f))

  orbit-monoid-action-Precategory : Precat l2 (l1 ⊔ l2)
  pr1 orbit-monoid-action-Precategory = type-Monoid-Action M X
  pr1 (pr2 orbit-monoid-action-Precategory) = hom-orbit-monoid-action-Set
  pr1 (pr1 (pr2 (pr2 orbit-monoid-action-Precategory))) =
    comp-hom-orbit-Monoid-Action
  pr2 (pr1 (pr2 (pr2 orbit-monoid-action-Precategory))) =
    associative-comp-hom-orbit-Monoid-Action
  pr1 (pr2 (pr2 (pr2 orbit-monoid-action-Precategory))) =
    id-hom-orbit-Monoid-Action
  pr1 (pr2 (pr2 (pr2 (pr2 orbit-monoid-action-Precategory)))) =
    left-unit-law-comp-hom-orbit-Monoid-Action
  pr2 (pr2 (pr2 (pr2 (pr2 orbit-monoid-action-Precategory)))) =
    right-unit-law-comp-hom-orbit-Monoid-Action

```
