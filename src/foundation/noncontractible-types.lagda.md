# Non-contractible types

```agda
module foundation.noncontractible-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.negation
```

</details>

## Idea

A type `X` is non-contractible if it comes equipped with an element of type
`¬ (is-contr X)`.

## Definitions

### The negation of being contractible

```agda
is-not-contractible : {l : Level} → UU l → UU l
is-not-contractible X = ¬ (is-contr X)
```

### A positive formulation of being noncontractible

Noncontractibility is a more positive way to prove that a type is not
contractible. When `A` is noncontractible in the following sense, then it is
apart from the unit type.

```agda
is-noncontractible' : {l : Level} (A : UU l) → ℕ → UU l
is-noncontractible' A zero-ℕ = is-empty A
is-noncontractible' A (succ-ℕ k) =
  Σ A (λ x → Σ A (λ y → is-noncontractible' (x ＝ y) k))

is-noncontractible : {l : Level} (A : UU l) → UU l
is-noncontractible A = Σ ℕ (is-noncontractible' A)
```

## Properties

### Empty types are not contractible

```agda
is-not-contractible-is-empty :
  {l : Level} {X : UU l} → is-empty X → is-not-contractible X
is-not-contractible-is-empty H C = H (center C)

is-not-contractible-empty : is-not-contractible empty
is-not-contractible-empty = is-not-contractible-is-empty id
```

### Noncontractible types are not contractible

```agda
is-not-contractible-is-noncontractible :
  {l : Level} {X : UU l} → is-noncontractible X → is-not-contractible X
is-not-contractible-is-noncontractible
  ( pair zero-ℕ H) = is-not-contractible-is-empty H
is-not-contractible-is-noncontractible (pair (succ-ℕ n) (pair x (pair y H))) C =
  is-not-contractible-is-noncontractible (pair n H) (is-prop-is-contr C x y)
```
