# Upper sets of large posets

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.upper-sets-large-posets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.large-posets funext
open import order-theory.large-subposets funext
```

</details>

## Idea

An **upper set** or **upwards closed set** in a
[large poset](order-theory.large-posets.md) is a
[large subposet](order-theory.large-subposets.md) that is upwards closed, i.e.,
that satisfies the condition that

```text
  ∀ (x y : P), (x ≤ y) → x ∈ S → y ∈ S.
```

## Definitions

### The predicate of being an upper set

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β) (S : Large-Subposet γ P)
  where

  is-upper-set-Large-Subposet : UUω
  is-upper-set-Large-Subposet =
    {l1 l2 : Level} (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    leq-Large-Poset P x y →
    is-in-Large-Subposet P S x → is-in-Large-Subposet P S y
```

### Upper sets of a large poset

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (P : Large-Poset α β)
  where

  record
    upper-set-Large-Poset : UUω
    where
    field
      large-subposet-upper-set-Large-Poset :
        Large-Subposet γ P
      is-upper-set-upper-set-Large-Poset :
        is-upper-set-Large-Subposet P large-subposet-upper-set-Large-Poset

  open upper-set-Large-Poset public
```

## See also

- [Lower sets](order-theory.lower-sets-large-posets.md)
- [Principal upper sets](order-theory.principal-upper-sets-large-posets.md)
