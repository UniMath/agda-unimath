# The precategory of orbits of a monoid action

```agda
module group-theory.precategory-of-orbits-monoid-actions where
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
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.monoid-actions
open import group-theory.monoids
```

</details>

## Idea

The [precategory](category-theory.precategories.md) of **orbits** of a
[monoid action](group-theory.monoid-actions.md) of `M` on `X` consists of the
elements of the [set](foundation-core.sets.md) `X` as the objects, and a
morphism from `x` to `y` is an element `m` of the
[monoid](group-theory.monoids.md) `M` such that `mx = y`.

## Definition

### The precategory of orbits of a monoid action

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (X : action-Monoid l2 M)
  where

  hom-orbit-action-Monoid : (x y : type-action-Monoid M X) → UU (l1 ⊔ l2)
  hom-orbit-action-Monoid x y =
    Σ (type-Monoid M) ( λ m → mul-action-Monoid M X m x ＝ y)

  element-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} → hom-orbit-action-Monoid x y → type-Monoid M
  element-hom-orbit-action-Monoid f = pr1 f

  eq-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    mul-action-Monoid M X (element-hom-orbit-action-Monoid f) x ＝ y
  eq-hom-orbit-action-Monoid f = pr2 f

  htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    UU l1
  htpy-hom-orbit-action-Monoid {x} {y} f g =
    Id
      ( element-hom-orbit-action-Monoid f)
      ( element-hom-orbit-action-Monoid g)

  refl-htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    htpy-hom-orbit-action-Monoid f f
  refl-htpy-hom-orbit-action-Monoid f = refl

  htpy-eq-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    f ＝ g → htpy-hom-orbit-action-Monoid f g
  htpy-eq-hom-orbit-action-Monoid f .f refl =
    refl-htpy-hom-orbit-action-Monoid f

  is-torsorial-htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    is-torsorial (htpy-hom-orbit-action-Monoid f)
  is-torsorial-htpy-hom-orbit-action-Monoid {x} {y} f =
    is-torsorial-Eq-subtype
      ( is-torsorial-Id (element-hom-orbit-action-Monoid f))
      ( λ u →
        is-set-type-action-Monoid M X (mul-action-Monoid M X u x) y)
      ( element-hom-orbit-action-Monoid f)
      ( refl)
      ( eq-hom-orbit-action-Monoid f)

  is-equiv-htpy-eq-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    is-equiv (htpy-eq-hom-orbit-action-Monoid f g)
  is-equiv-htpy-eq-hom-orbit-action-Monoid f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-orbit-action-Monoid f)
      ( htpy-eq-hom-orbit-action-Monoid f)

  extensionality-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    (f ＝ g) ≃ htpy-hom-orbit-action-Monoid f g
  pr1 (extensionality-hom-orbit-action-Monoid f g) =
    htpy-eq-hom-orbit-action-Monoid f g
  pr2 (extensionality-hom-orbit-action-Monoid f g) =
    is-equiv-htpy-eq-hom-orbit-action-Monoid f g

  eq-htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} {f g : hom-orbit-action-Monoid x y} →
    htpy-hom-orbit-action-Monoid f g → f ＝ g
  eq-htpy-hom-orbit-action-Monoid {x} {y} {f} {g} =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-orbit-action-Monoid f g)

  is-prop-htpy-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f g : hom-orbit-action-Monoid x y) →
    is-prop (htpy-hom-orbit-action-Monoid f g)
  is-prop-htpy-hom-orbit-action-Monoid f g =
    is-set-type-Monoid M
      ( element-hom-orbit-action-Monoid f)
      ( element-hom-orbit-action-Monoid g)

  is-set-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} →
    is-set (hom-orbit-action-Monoid x y)
  is-set-hom-orbit-action-Monoid {x} {y} f g =
    is-prop-equiv
      ( extensionality-hom-orbit-action-Monoid f g)
      ( is-prop-htpy-hom-orbit-action-Monoid f g)

  hom-orbit-monoid-action-Set :
    (x y : type-action-Monoid M X) → Set (l1 ⊔ l2)
  pr1 (hom-orbit-monoid-action-Set x y) = hom-orbit-action-Monoid x y
  pr2 (hom-orbit-monoid-action-Set x y) = is-set-hom-orbit-action-Monoid

  id-hom-orbit-action-Monoid :
    (x : type-action-Monoid M X) → hom-orbit-action-Monoid x x
  pr1 (id-hom-orbit-action-Monoid x) = unit-Monoid M
  pr2 (id-hom-orbit-action-Monoid x) = unit-law-mul-action-Monoid M X x

  comp-hom-orbit-action-Monoid :
    {x y z : type-action-Monoid M X} →
    hom-orbit-action-Monoid y z → hom-orbit-action-Monoid x y →
    hom-orbit-action-Monoid x z
  pr1 (comp-hom-orbit-action-Monoid g f) =
    mul-Monoid M
      ( element-hom-orbit-action-Monoid g)
      ( element-hom-orbit-action-Monoid f)
  pr2 (comp-hom-orbit-action-Monoid {x} g f) =
    ( associative-mul-action-Monoid M X
      ( element-hom-orbit-action-Monoid g)
      ( element-hom-orbit-action-Monoid f)
      ( x)) ∙
    ( ap-mul-action-Monoid M X (eq-hom-orbit-action-Monoid f)) ∙
    ( eq-hom-orbit-action-Monoid g)

  associative-comp-hom-orbit-action-Monoid :
    {x y z w : type-action-Monoid M X} (h : hom-orbit-action-Monoid z w)
    (g : hom-orbit-action-Monoid y z) (f : hom-orbit-action-Monoid x y) →
    comp-hom-orbit-action-Monoid (comp-hom-orbit-action-Monoid h g) f ＝
    comp-hom-orbit-action-Monoid h (comp-hom-orbit-action-Monoid g f)
  associative-comp-hom-orbit-action-Monoid h g f =
    eq-htpy-hom-orbit-action-Monoid
      ( associative-mul-Monoid M
        ( element-hom-orbit-action-Monoid h)
        ( element-hom-orbit-action-Monoid g)
        ( element-hom-orbit-action-Monoid f))

  left-unit-law-comp-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    comp-hom-orbit-action-Monoid (id-hom-orbit-action-Monoid y) f ＝ f
  left-unit-law-comp-hom-orbit-action-Monoid f =
    eq-htpy-hom-orbit-action-Monoid
      ( left-unit-law-mul-Monoid M (element-hom-orbit-action-Monoid f))

  right-unit-law-comp-hom-orbit-action-Monoid :
    {x y : type-action-Monoid M X} (f : hom-orbit-action-Monoid x y) →
    comp-hom-orbit-action-Monoid f (id-hom-orbit-action-Monoid x) ＝ f
  right-unit-law-comp-hom-orbit-action-Monoid f =
    eq-htpy-hom-orbit-action-Monoid
      ( right-unit-law-mul-Monoid M (element-hom-orbit-action-Monoid f))

  orbit-monoid-action-Precategory : Precategory l2 (l1 ⊔ l2)
  orbit-monoid-action-Precategory =
    make-Precategory
      ( type-action-Monoid M X)
      ( hom-orbit-monoid-action-Set)
      ( comp-hom-orbit-action-Monoid)
      ( id-hom-orbit-action-Monoid)
      ( associative-comp-hom-orbit-action-Monoid)
      ( left-unit-law-comp-hom-orbit-action-Monoid)
      ( right-unit-law-comp-hom-orbit-action-Monoid)
```
