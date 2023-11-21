# Cd-structures

```agda
module orthogonal-factorization-systems.cd-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.morphisms-arrows
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **cd-structure** on a [category](category-theory.categories.md) consists of a
class `𝒟` of **distinguished squares**

```text
        i
    A -----> X
    |        |
  f |        | g
    V        V
    B -----> Y.
        j
```

On this page we will consider **(internal) cd-structures**, i.e., cd-structure
on types. In other words, a cd-structure is a family of
[subtypes](foundation-core.subtypes.md)

```text
  (f : A → B) (g : X → Y) → hom-arrow f g → Prop,
```

where `hom-arrow f g` is the type of
[morphisms of arrows](foundation.morphisms-arrows.md) from `f` to `g`.

## Definitions

### Cd-structures

```agda
module _
  (α : Level → Level → Level → Level → Level)
  where

  cd-structure : UUω
  cd-structure =
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} →
    (f : A → B) (g : X → Y) → subtype (α l1 l2 l3 l4) (hom-arrow f g)
```
