# Binary relations with lifts

```agda
module foundation.binary-relations-with-lifts where
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

We say a [relation](foundation.binary-relations.md) `R`
{{#concept "has lifts" Disambiguation="binary relations of types" Agda=has-lifts-Relation}}
if for every triple `x y z : A`, there is a binary operation

```text
  R x z → R y z → R x y.
```

Relations with lifts are closely related to transitive relations. But, instead
of giving for every diagram

```text
       y
      ∧ \
     /   \
    /     ∨
  x        z
```

a horizontal arrow `x → z`, a binary relation with lifts gives, for every cospan

```text
       y
        \
         \
          ∨
  x -----> z,
```

a _lift_ `x → y`. By symmetry it also gives a lift in the opposite direction
`y → x`.

Dually, a relation `R`
[has extensions](foundation.binary-relations-with-extensions.md) if for every
triple `x y z : A`, there is a binary operation

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

## Properties

### If `x` relates to an element and the relation has lifts, then `x` relates to `x`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  rel-self-rel-any-has-lifts-Relation :
    has-lifts-Relation R → {x y : A} → R x y → R x x
  rel-self-rel-any-has-lifts-Relation H p = H p p
```

### The reverse of a lift

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  reverse-has-lifts-Relation :
    has-lifts-Relation R → {x y z : A} → R x z → R y z → R y x
  reverse-has-lifts-Relation H p q = H q p
```

### Reflexive relations with lifts are symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (H : has-lifts-Relation R)
  where

  is-symmetric-is-reflexive-has-lifts-Relation :
    is-reflexive R → is-symmetric R
  is-symmetric-is-reflexive-has-lifts-Relation r x y p = H (r y) p
```

### Reflexive relations with lifts are transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (H : has-lifts-Relation R)
  where

  is-transitive-is-symmetric-has-lifts-Relation :
    is-symmetric R → is-transitive R
  is-transitive-is-symmetric-has-lifts-Relation s x y z p q = H q (s y z p)

  is-transitive-is-reflexive-has-lifts-Relation :
    is-reflexive R → is-transitive R
  is-transitive-is-reflexive-has-lifts-Relation r =
    is-transitive-is-symmetric-has-lifts-Relation
      ( is-symmetric-is-reflexive-has-lifts-Relation R H r)
```
