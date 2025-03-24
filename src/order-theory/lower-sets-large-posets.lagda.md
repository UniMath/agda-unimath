# Lower sets in large posets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.lower-sets-large-posets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.large-posets funext univalence truncations
open import order-theory.large-subposets funext univalence truncations
```

</details>

## Idea

A **lower set** or **downwards closed set** in a
[large poset](order-theory.large-posets.md) is a
[large subposet](order-theory.large-subposets.md) that is downwards closed,
i.e., that satisfies the condition that

```text
  ∀ (x y : P), (y ≤ x) → x ∈ S → y ∈ S.
```

## Definitions

### The predicate of being a lower set

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β) (S : Large-Subposet γ P)
  where

  is-lower-set-Large-Subposet : UUω
  is-lower-set-Large-Subposet =
    {l1 l2 : Level} (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    leq-Large-Poset P y x →
    is-in-Large-Subposet P S x → is-in-Large-Subposet P S y
```

### Lower sets of a large poset

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (P : Large-Poset α β)
  where

  record
    lower-set-Large-Poset : UUω
    where
    field
      large-subposet-lower-set-Large-Poset :
        Large-Subposet γ P
      is-lower-set-lower-set-Large-Poset :
        is-lower-set-Large-Subposet P large-subposet-lower-set-Large-Poset

  open lower-set-Large-Poset public

module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β) (L : lower-set-Large-Poset γ P)
  where

  is-in-lower-set-Large-Poset :
    {l : Level} (x : type-Large-Poset P l) → UU (γ l)
  is-in-lower-set-Large-Poset =
    is-in-Large-Subposet P (large-subposet-lower-set-Large-Poset L)
```

## See also

- [Principal lower sets](order-theory.principal-lower-sets-large-posets.md)
- [Upper sets](order-theory.upper-sets-large-posets.md)
