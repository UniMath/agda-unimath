# Trivial group homomorphisms

```agda
module group-theory.trivial-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
```

</details>

## Idea

A **trivial group homomorphism** from `G` to `H` is a
[group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` such that
`f x ＝ 1` for every `x : G`.

## Definitions

### The predicate of being a trivial group homomorphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-trivial-prop-hom-Group : Prop (l1 ⊔ l2)
  is-trivial-prop-hom-Group =
    Π-Prop
      ( type-Group G)
      ( λ x → Id-Prop (set-Group H) (map-hom-Group G H f x) (unit-Group H))

  is-trivial-hom-Group : UU (l1 ⊔ l2)
  is-trivial-hom-Group = type-Prop is-trivial-prop-hom-Group

  is-prop-is-trivial-hom-Group : is-prop is-trivial-hom-Group
  is-prop-is-trivial-hom-Group = is-prop-type-Prop is-trivial-prop-hom-Group
```

### The trivial group homomorphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  trivial-hom-Group : hom-Group G H
  pr1 trivial-hom-Group x = unit-Group H
  pr2 trivial-hom-Group x y = inv (left-unit-law-mul-Group H (unit-Group H))
```
