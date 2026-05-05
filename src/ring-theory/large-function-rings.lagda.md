# Large function rings

```agda
module ring-theory.large-function-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.universe-levels

open import group-theory.large-function-abelian-groups

open import ring-theory.large-rings
```

</details>

## Idea

Given a [large ring](ring-theory.large-rings.md) `R` and an arbitrary type `A`,
`A → R` forms a large ring.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (R : Large-Ring α β)
  where

  function-Large-Ring : Large-Ring (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  large-ab-Large-Ring function-Large-Ring =
    function-Large-Ab A (large-ab-Large-Ring R)
  mul-Large-Ring function-Large-Ring f g a = mul-Large-Ring R (f a) (g a)
  preserves-sim-mul-Large-Ring function-Large-Ring f f' f~f' g g' g~g' a =
    preserves-sim-mul-Large-Ring R (f a) (f' a) (f~f' a) (g a) (g' a) (g~g' a)
  one-Large-Ring function-Large-Ring a = one-Large-Ring R
  associative-mul-Large-Ring function-Large-Ring f g h =
    eq-htpy (λ a → associative-mul-Large-Ring R (f a) (g a) (h a))
  left-unit-law-mul-Large-Ring function-Large-Ring f =
    eq-htpy (λ a → left-unit-law-mul-Large-Ring R (f a))
  right-unit-law-mul-Large-Ring function-Large-Ring f =
    eq-htpy (λ a → right-unit-law-mul-Large-Ring R (f a))
  left-distributive-mul-add-Large-Ring function-Large-Ring f g h =
    eq-htpy (λ a → left-distributive-mul-add-Large-Ring R (f a) (g a) (h a))
  right-distributive-mul-add-Large-Ring function-Large-Ring f g h =
    eq-htpy (λ a → right-distributive-mul-add-Large-Ring R (f a) (g a) (h a))
```
