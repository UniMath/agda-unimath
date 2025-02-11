# The precategory of posets

```agda
module order-theory.precategory-of-posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

The {{#concept "(large) precategory of posets" Agda=Poset-Large-Precategory}}
consists of [posets](order-theory.posets.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md).

## Definitions

### The large precategory of posets

**Remark.** In this formalization we see a clear limit to our approach using
[large precategories](category-theory.large-precategories.md). Large
precategories are only designed to encapsulate structures that are universe
polymorphic in a single universe level variable. However, posets are polymorphic
in two universe level variables, leading to a shortcoming in the below
formalization. Namely, we cannot capture the structure of all posets and
morphisms between them. For instance, we can only capture morphisms between two
posets of the form `A : Poset (α l1) (β l1)` and `B : Poset (α l2) (β l2)`, and
not arbitrary ones of the form `A : Poset l1 l2` and `B : Poset l3 l4`.

```agda
parametric-Poset-Large-Precategory :
  (α β : Level → Level) →
  Large-Precategory
    ( λ l → lsuc (α l) ⊔ lsuc (β l))
    ( λ l1 l2 → α l1 ⊔ β l1 ⊔ α l2 ⊔ β l2)
parametric-Poset-Large-Precategory α β =
  λ where
    .obj-Large-Precategory l →
      Poset (α l) (β l)
    .hom-set-Large-Precategory →
      hom-set-Poset
    .comp-hom-Large-Precategory {X = X} {Y} {Z} →
      comp-hom-Poset X Y Z
    .id-hom-Large-Precategory {X = X} →
      id-hom-Poset X
    .involutive-eq-associative-comp-hom-Large-Precategory {X = X} {Y} {Z} {W} →
      involutive-eq-associative-comp-hom-Poset X Y Z W
    .left-unit-law-comp-hom-Large-Precategory {X = X} {Y} →
      left-unit-law-comp-hom-Poset X Y
    .right-unit-law-comp-hom-Large-Precategory {X = X} {Y} →
      right-unit-law-comp-hom-Poset X Y

Poset-Large-Precategory : Large-Precategory lsuc (_⊔_)
Poset-Large-Precategory = parametric-Poset-Large-Precategory (λ l → l) (λ l → l)
```

### The precategory of posets at a universe level

```agda
Poset-Precategory : (l1 l2 : Level) → Precategory (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
Poset-Precategory l1 l2 =
  make-Precategory
    ( Poset l1 l2)
    ( hom-set-Poset)
    ( λ {P} {Q} {R} → comp-hom-Poset P Q R)
    ( id-hom-Poset)
    ( λ {P} {Q} {R} {S} → associative-comp-hom-Poset P Q R S)
    ( λ {P} {Q} → left-unit-law-comp-hom-Poset P Q)
    ( λ {P} {Q} → right-unit-law-comp-hom-Poset P Q)
```
