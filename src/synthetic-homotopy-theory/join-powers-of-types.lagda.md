# Join powers of types

```agda
open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.join-powers-of-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.empty-types funext
open import foundation.iterating-functions funext
open import foundation.universe-levels

open import synthetic-homotopy-theory.joins-of-types funext
```

</details>

## Idea

The `n`-th **join power** of a type `A` is defined by taking the
[`n`-fold](foundation.iterating-functions.md)
[join](synthetic-homotopy-theory.joins-of-types.md) of `A` with itself.

## Definitions

### Join powers of types

```agda
join-power : {l1 : Level} → ℕ → UU l1 → UU l1
join-power n A = iterate n (join A) (raise-empty _)
```

### Join powers of type families

```agda
join-power-family-of-types :
  {l1 l2 : Level} → ℕ → {A : UU l1} → (A → UU l2) → (A → UU l2)
join-power-family-of-types n B a = join-power n (B a)
```
