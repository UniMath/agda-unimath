# Surjective group homomorphisms

```agda
module group-theory.surjective-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
```

</details>

A [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` is said
to be **surjective** if its underlying map is
[surjective](foundation.surjective-maps.md)

## Definition

### Surjective group homomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-surjective-prop-hom-Group : Prop (l1 ⊔ l2)
  is-surjective-prop-hom-Group = is-surjective-Prop (map-hom-Group G H f)

  is-surjective-hom-Group : UU (l1 ⊔ l2)
  is-surjective-hom-Group = type-Prop is-surjective-prop-hom-Group

  is-prop-is-surjective-hom-Group : is-prop is-surjective-hom-Group
  is-prop-is-surjective-hom-Group =
    is-prop-type-Prop is-surjective-prop-hom-Group
```
