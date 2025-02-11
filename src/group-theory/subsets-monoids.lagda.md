# Subsets of monoids

```agda
module group-theory.subsets-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.monoids
```

</details>

## Idea

A subset of a monoid `M` is a subset of the underlying type of `M`.

## Definitions

### Subsets of monoids

```agda
subset-Monoid :
  {l1 : Level} (l2 : Level) (M : Monoid l1) → UU (l1 ⊔ lsuc l2)
subset-Monoid l2 M = subtype l2 (type-Monoid M)

module _
  {l1 l2 : Level} (M : Monoid l1) (P : subset-Monoid l2 M)
  where

  is-in-subset-Monoid : type-Monoid M → UU l2
  is-in-subset-Monoid = is-in-subtype P

  is-prop-is-in-subset-Monoid :
    (x : type-Monoid M) → is-prop (is-in-subset-Monoid x)
  is-prop-is-in-subset-Monoid = is-prop-is-in-subtype P

  type-subset-Monoid : UU (l1 ⊔ l2)
  type-subset-Monoid = type-subtype P

  is-set-type-subset-Monoid : is-set type-subset-Monoid
  is-set-type-subset-Monoid =
    is-set-type-subtype P (is-set-type-Monoid M)

  set-subset-Monoid : Set (l1 ⊔ l2)
  set-subset-Monoid = set-subset (set-Monoid M) P

  inclusion-subset-Monoid : type-subset-Monoid → type-Monoid M
  inclusion-subset-Monoid = inclusion-subtype P

  ap-inclusion-subset-Monoid :
    (x y : type-subset-Monoid) →
    x ＝ y → (inclusion-subset-Monoid x ＝ inclusion-subset-Monoid y)
  ap-inclusion-subset-Monoid = ap-inclusion-subtype P

  is-in-subset-inclusion-subset-Monoid :
    (x : type-subset-Monoid) →
    is-in-subset-Monoid (inclusion-subset-Monoid x)
  is-in-subset-inclusion-subset-Monoid =
    is-in-subtype-inclusion-subtype P
```

### The condition that a subset contains the unit

```agda
  contains-unit-prop-subset-Monoid : Prop l2
  contains-unit-prop-subset-Monoid = P (unit-Monoid M)

  contains-unit-subset-Monoid : UU l2
  contains-unit-subset-Monoid = type-Prop contains-unit-prop-subset-Monoid
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-prop-subset-Monoid : Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-subset-Monoid =
    Π-Prop
      ( type-Monoid M)
      ( λ x →
        Π-Prop
          ( type-Monoid M)
          ( λ y → hom-Prop (P x) (hom-Prop (P y) (P (mul-Monoid M x y)))))

  is-closed-under-multiplication-subset-Monoid : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Monoid =
    type-Prop is-closed-under-multiplication-prop-subset-Monoid
```
