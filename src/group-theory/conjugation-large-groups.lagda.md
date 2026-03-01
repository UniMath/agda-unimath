# Conjugation in large groups

```agda
module group-theory.conjugation-large-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.large-groups
```

</details>

## Idea

{{#concept "Conjugation" Disambiguation="in large groups" Agda=left-conjugation-Large-Group}}
by an element `x` in a [large group](group-theory.large-groups.md) `G` is the
map `y ↦ (xy)x⁻¹`.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Group α β)
  where

  left-conjugation-Large-Group :
    {l1 l2 : Level} →
    type-Large-Group G l1 → type-Large-Group G l2 →
    type-Large-Group G (l1 ⊔ l2)
  left-conjugation-Large-Group x y =
    mul-Large-Group G (mul-Large-Group G x y) (inv-Large-Group G x)

  right-conjugation-Large-Group :
    {l1 l2 : Level} →
    type-Large-Group G l1 → type-Large-Group G l2 →
    type-Large-Group G (l1 ⊔ l2)
  right-conjugation-Large-Group x y =
    mul-Large-Group G x (mul-Large-Group G y (inv-Large-Group G x))
```

## Properties

### Left and right conjugation are equivalent

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Group α β)
  where

  abstract
    eq-left-right-conjugation-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      left-conjugation-Large-Group G x y ＝ right-conjugation-Large-Group G x y
    eq-left-right-conjugation-Large-Group x y =
      associative-mul-Large-Group G x y (inv-Large-Group G x)
```

## See also

- [Conjugation in (small) groups](group-theory.conjugation.md)
