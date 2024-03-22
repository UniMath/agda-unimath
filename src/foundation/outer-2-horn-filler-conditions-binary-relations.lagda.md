# Outer 2-horn filler conditions for binary relations

```agda
module foundation.outer-2-horn-filler-conditions-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

We say a [relation](foundation.binary-relations.md) `R` has
{{#concept "lifts" Disambiguation="binary relations of types" Agda=has-lifts-Relation}}
if for every triple `x y z : A`, there is a binary operation

```text
  R x z → R y z → R x y.
```

Relations with lifts are closely related to transitive relations. But, instead
of giving for every diagram

```text
        y
       ∧ \
     /    \
    /      ∨
  x         z
```

a horizontal arrow

```text
        y
       ∧ \
     /    \
    /      ∨
  x - - - > z,
```

a binary relation with lifts gives for every cospan

```text
        y
         \
          \
           ∨
  x ------> z
```

a lift

```text
        y
       ∧ \
      ⋰   \
    ⋰      ∨
  x ------> z.
```

**Note.** By symmetry it also gives a lift in the opposite direction

```text
        y
      ⋰ \
    ⋰    \
   ∨       ∨
  x ------> z.
```

Dually, a relation `R` has
{{#concept "extensions" Disambiguation="binary relations of types"  Agda=has-extensions-Relation}}
if for every triple `x y z : A`, there is a binary operation

```text
  R x y → R x z → R y z.
```

## Definition

### The structure on relations of having lifts

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  has-lifts-Relation : UU (l1 ⊔ l2)
  has-lifts-Relation = {x y z : A} → R x z → R y z → R x y
```

### The structure on relations of having extensions

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  has-extensions-Relation : UU (l1 ⊔ l2)
  has-extensions-Relation = {x y z : A} → R x y → R x z → R y z
```

## Properties

### If there is an element that relates to `y` then `y` relates to `y`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  rel-self-any-rel-has-extensions-Relation :
    has-extensions-Relation R → {x y : A} → R x y → R y y
  rel-self-any-rel-has-extensions-Relation H p = H p p
```

### The reverse of an extension

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  reverse-has-extensions-Relation :
    has-extensions-Relation R → {x y z : A} → R z x → R z y → R y x
  reverse-has-extensions-Relation H p q = H q p
```

### Reflexive relations with extensions are symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (H : has-extensions-Relation R)
  where

  is-symmetric-is-reflexive-has-extensions-Relation :
    is-reflexive R → is-symmetric R
  is-symmetric-is-reflexive-has-extensions-Relation r x y p =
    H p (r x)
```

### Reflexive relations with extensions satisfy all 2-horn filler conditions

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (H : has-extensions-Relation R)
  where

  is-transitive-is-symmetric-has-extensions-Relation :
    is-symmetric R → is-transitive R
  is-transitive-is-symmetric-has-extensions-Relation s x y z p q =
    H (s x y q) p

  is-transitive-is-reflexive-has-extensions-Relation :
    is-reflexive R → is-transitive R
  is-transitive-is-reflexive-has-extensions-Relation r =
    is-transitive-is-symmetric-has-extensions-Relation
      ( is-symmetric-is-reflexive-has-extensions-Relation R H r)
```

## See also

- [Strict symmetrization of binary relations](foundation.strict-symmetrization-binary-relations.md)
