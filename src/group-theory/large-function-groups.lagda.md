# Large function groups

```agda
module group-theory.large-function-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.universe-levels

open import group-theory.large-function-monoids
open import group-theory.large-groups
```

</details>

## Idea

Given a [large group](group-theory.large-groups.md) `G` and an arbitrary type
`A`, `A → G` forms a large group.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (G : Large-Group α β)
  where

  function-Large-Group : Large-Group (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  large-monoid-Large-Group function-Large-Group =
    function-Large-Monoid A (large-monoid-Large-Group G)
  inv-Large-Group function-Large-Group f a = inv-Large-Group G (f a)
  preserves-sim-inv-Large-Group function-Large-Group f g f~g a =
    preserves-sim-inv-Large-Group G (f a) (g a) (f~g a)
  left-inverse-law-mul-Large-Group function-Large-Group f =
    eq-htpy (λ a → left-inverse-law-mul-Large-Group G (f a))
  right-inverse-law-mul-Large-Group function-Large-Group f =
    eq-htpy (λ a → right-inverse-law-mul-Large-Group G (f a))
```
