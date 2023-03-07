# Pointed types

```agda
module structured-types.pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A pointed type is a type `A` equipped with an element `a : A`.

## Definition

### The universe of pointed types

```agda
Pointed-Type : (l : Level) → UU (lsuc l)
Pointed-Type l = Σ (UU l) (λ X → X)

module _
  {l : Level} (A : Pointed-Type l)
  where

  type-Pointed-Type : UU l
  type-Pointed-Type = pr1 A

  pt-Pointed-Type : type-Pointed-Type
  pt-Pointed-Type = pr2 A
```

### Evaluation at the base point

```agda
ev-pt-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) {B : UU l2} →
  (type-Pointed-Type A → B) → B
ev-pt-Pointed-Type A f = f (pt-Pointed-Type A)
```

## See also

- The notion of *nonempty types* is treated in
  [`foundation.empty-types`](foundation.empty-types.md).

- The notion of *inhabited types* is treated in
  [`foundation.inhabited-types`](foundation.inhabited-types.md).
