# Upper bounds for type families over the natural numbers

```agda
module elementary-number-theory.upper-bounds-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.universe-levels
```

</details>

## Idea

A type family over the
[natural numbers](elementary-number-theory.natural-numbers.md) has an
{{#concept "upper bound" Disambiguation="of a type family over ℕ" Agda=is-upper-bound-ℕ}}
`n`, if there is a function from `P x` to the type `x ≤ n` for all `x : ℕ`.
Analogously, a
{{#concept "strict upper bound" Disambiguation="of a type family over ℕ" Agda=is-strict-upper-bound-ℕ}}
is defined by a function from `P x` to the type `x < n` for all `x : ℕ`.

## Definition

### Upper bounds

```agda
is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-upper-bound-ℕ P n =
  (m : ℕ) → P m → leq-ℕ m n
```

### Strict upper bounds

```agda
is-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-strict-upper-bound-ℕ P n =
  (m : ℕ) → P m → le-ℕ m n
```

## Properties

### A strict upper bound is an upper bound

```agda
is-upper-bound-is-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-strict-upper-bound-ℕ P n → is-upper-bound-ℕ P n
is-upper-bound-is-strict-upper-bound-ℕ P n H x p =
  leq-le-ℕ x n (H x p)
```
