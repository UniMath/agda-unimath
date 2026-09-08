# Transposition of grids

```agda
module linear-algebra.transposition-grids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.grids

open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

The
{{#concept "transposition of a grid" WD="grid transposition" WDID=Q77961711 Agda=transpose-grid}}
is the operation on [grids](linear-algebra.grids.md) that turns rows into
columns and columns into rows.

## Definition

```agda
transpose-grid :
  {l : Level} → {A : UU l} → {m n : ℕ} → grid A m n → grid A n m
transpose-grid {n = zero-ℕ} x = empty-tuple
transpose-grid {n = succ-ℕ n} x =
  map-tuple head-tuple x ∷ transpose-grid (map-tuple tail-tuple x)
```

## Properties

```agda
is-involution-transpose-grid :
  {l : Level} → {A : UU l} → {m n : ℕ} →
  (x : grid A m n) → x ＝ transpose-grid (transpose-grid x)
is-involution-transpose-grid {m = zero-ℕ} empty-tuple = refl
is-involution-transpose-grid {m = succ-ℕ m} (r ∷ rs) =
  ( ap (_∷_ r) (is-involution-transpose-grid rs)) ∙
  ( ap-binary _∷_
    ( lemma-first-row r rs) (ap transpose-grid (lemma-rest r rs)))
  where
  lemma-first-row :
    {l : Level} → {A : UU l} → {m n : ℕ} → (x : tuple A n) →
    (xs : grid A m n) →
    x ＝ map-tuple head-tuple (transpose-grid (x ∷ xs))
  lemma-first-row {n = zero-ℕ} empty-tuple _ = refl
  lemma-first-row {n = succ-ℕ m} (k ∷ ks) xs =
    ap (_∷_ k) (lemma-first-row ks (map-tuple tail-tuple xs))

  lemma-rest :
    {l : Level} → {A : UU l} → {m n : ℕ} → (x : tuple A n) →
    (xs : grid A m n) →
    transpose-grid xs ＝ map-tuple tail-tuple (transpose-grid (x ∷ xs))
  lemma-rest {n = zero-ℕ} empty-tuple xs = refl
  lemma-rest {n = succ-ℕ n} (k ∷ ks) xs =
    ap
      ( _∷_ (map-tuple head-tuple xs))
      ( lemma-rest (tail-tuple (k ∷ ks)) (map-tuple tail-tuple xs))
```
