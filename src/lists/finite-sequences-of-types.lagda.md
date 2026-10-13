# Finite sequences of types

```agda
module lists.finite-sequences-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.universe-levels

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [finite sequence](lists.finite-sequences.md) of types `A : Fin n → UU l`
induces a type `Πₙ A = (i : Fin n) → A i`, i.e.,

```text
  Πₙ A ≃ A₀ × A₁ × ... × Aᵢ × ... Aₙ₋₁
```

For any [natural number](elementary-number-theory.natural-numbers.md) `n`, and
and any [index](univalent-combinatorics.standard-finite-types.md)
`i : Fin (n+1)`,

```text
  Πₙ₊₁ A ≃ Aᵢ × Πₙ Aⁱ
```

where `Aⁱ` denotes the finite sequence of types obtained by
[removing](lists.remove-at-index-finite-sequences.md) the `i`th component of `A`
so `Πₙ Aⁱ = A₀ × ... Aᵢ₋₁ × Aᵢ₊ᵢ × ... × Aₙ`.

## Definition

### Elements of a finite product of types

```agda
module _
  {l : Level} (n : ℕ) (A : Fin n → UU l)
  where

  Π-fin-sequence : UU l
  Π-fin-sequence = (i : Fin n) → A i
```

## Properties

### Coordinate maps of finite products

```agda
module _
  {l : Level} (n : ℕ) (A : Fin n → UU l)
  where

  elem-at-Π-fin-sequence :
    (i : Fin n) → Π-fin-sequence n A → A i
  elem-at-Π-fin-sequence i u = u i
```

### Tails of a finite product of types

```agda
module _
  {l : Level} (n : ℕ) (A : fin-sequence (UU l) (succ-ℕ n))
  where

  tail-Π-fin-sequence :
    Π-fin-sequence (succ-ℕ n) A →
    Π-fin-sequence n (tail-fin-sequence n A)
  tail-Π-fin-sequence u = u ∘ inl-Fin n
```
