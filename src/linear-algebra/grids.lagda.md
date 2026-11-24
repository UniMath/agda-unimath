# Grids

```agda
module linear-algebra.grids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

An `m × n` {{#concept "grid" Agda=grid}} of elements in `A` is a
[tuple](lists.tuples.md) of length `m` of tuples of length `n` of elements of
`A`. In other words, a grid is an arrangement of elements of `A` with `m` rows
and `n` columns.

## Definitions

### Grids

```agda
grid : {l : Level} (A : UU l) → ℕ → ℕ → UU l
grid A m n = tuple (tuple A n) m
```

### The top row of a grid

```agda
top-row-grid :
  {l : Level} {m n : ℕ} {A : UU l} → grid A (succ-ℕ m) n → tuple A n
top-row-grid (v ∷ M) = v
```

### The left column of a grid

```agda
left-column-grid :
  {l : Level} {m n : ℕ} {A : UU l} → grid A m (succ-ℕ n) → tuple A m
left-column-grid = map-tuple head-tuple
```

### The vertical tail of a grid

```agda
vertical-tail-grid :
  {l : Level} {m n : ℕ} {A : UU l} → grid A (succ-ℕ m) n → grid A m n
vertical-tail-grid M = tail-tuple M
```

### The horizontal tail of a grid

```agda
horizontal-tail-grid :
  {l : Level} {m n : ℕ} {A : UU l} → grid A m (succ-ℕ n) → grid A m n
horizontal-tail-grid = map-tuple tail-tuple
```

### The vertically empty grid

```agda
vertically-empty-grid :
  {l : Level} {n : ℕ} {A : UU l} → grid A 0 n
vertically-empty-grid = empty-tuple

eq-vertically-empty-grid :
  {l : Level} {n : ℕ} {A : UU l}
  (x : grid A 0 n) → vertically-empty-grid ＝ x
eq-vertically-empty-grid empty-tuple = refl

is-contr-grid-zero-ℕ :
  {l : Level} {n : ℕ} {A : UU l} → is-contr (grid A 0 n)
pr1 is-contr-grid-zero-ℕ = vertically-empty-grid
pr2 is-contr-grid-zero-ℕ = eq-vertically-empty-grid
```

### The horizontally empty grid

```agda
horizontally-empty-grid :
  {l : Level} {m : ℕ} {A : UU l} → grid A m 0
horizontally-empty-grid {m = zero-ℕ} = empty-tuple
horizontally-empty-grid {m = succ-ℕ m} =
  empty-tuple ∷ horizontally-empty-grid

eq-horizontally-empty-grid :
  {l : Level} {m : ℕ} {A : UU l}
  (x : grid A m 0) → horizontally-empty-grid ＝ x
eq-horizontally-empty-grid {m = zero-ℕ} empty-tuple = refl
eq-horizontally-empty-grid {m = succ-ℕ m} (empty-tuple ∷ M) =
  ap-binary _∷_ refl (eq-horizontally-empty-grid M)

is-contr-grid-zero-ℕ' :
  {l : Level} {m : ℕ} {A : UU l} → is-contr (grid A m 0)
pr1 is-contr-grid-zero-ℕ' = horizontally-empty-grid
pr2 is-contr-grid-zero-ℕ' = eq-horizontally-empty-grid
```

## See also

- [Matrices](linear-algebra.matrices.md), the analogous concept but with
  [finite sequences](lists.finite-sequences.md) in the role of
  [tuples](lists.tuples.md)
