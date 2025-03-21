# Commuting squares of group homomorphisms

```agda
module group-theory.commuting-squares-of-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
```

</details>

## Idea

A square of [group homomorphisms](group-theory.homomorphisms-groups.md)

```text
        f
    G -----> H
    |        |
  g |        | h
    ∨        ∨
    K -----> L
        k
```

is said to **commute** if the underlying square of maps
[commutes](foundation.commuting-squares-of-maps.md), i.e., if `k ∘ g ~ h ∘ f`.

## Definitions

### Commuting squares of group homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3) (L : Group l4)
  (f : hom-Group G H) (g : hom-Group G K)
  (h : hom-Group H L) (k : hom-Group K L)
  where

  coherence-square-hom-Group : UU (l1 ⊔ l4)
  coherence-square-hom-Group =
    coherence-square-maps
      ( map-hom-Group G H f)
      ( map-hom-Group G K g)
      ( map-hom-Group H L h)
      ( map-hom-Group K L k)
```
