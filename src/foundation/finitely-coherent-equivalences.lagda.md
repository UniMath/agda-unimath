# Finitely coherent equivalences

```agda
module foundation.finitely-coherent-equivalences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

Any map `f : A → B` is said to be a `0`-coherent equivalence.
Furthermore, a map `f : A → B` is said to be a `n + 1`-coherent equivalence if
it comes equipped with map `g : B → A` and a family of maps

```text
  r x y : (f x ＝ y) → (x ＝ g y)
```

indexed by `x : A` and `y : B`, such that each `r x y` is an `n`-coherent equivalence.

A `1`-coherent equivalence is therefore a map equipped with a [retraction](foundation-core.retractions.md). A `2`-coherent equivalence is a map `f : A → B` equipped with `g : B → A` and for each `x : A` and `y : B` a map `r x y : (f x ＝ y) → (x ＝ g y)`, equipped with

```text
  s x y : (x ＝ g y) → (f x ＝ y)
```

and for each `p : f x ＝ y` and `q : x ＝ g y` a map

```text
  t p q : (r x y p ＝ q) → (p ＝ s x y q)
```

This data is equivalent to the data of a [coherently invertible map](foundation-core.coherently-invertible-maps.md)

```text
  r : (x : A) → g (f x) ＝ x
  s : (y : B) → f (g y) ＝ y
  t : (x : A) → ap f (r x) ＝ s (f x)
```

The condition of being an `n`-coherent equivalent is a [proposition](foundation-core.propositions.md) for each `n ≥ 2`, and this proposition is equivalent to being an equivalence.

## Definitions

### The predicate of being an `n`-coherent equivalence

```agda
data
  is-coherent-equivalence
    {l1 l2 : Level}  {A : UU l1} {B : UU l2} :
    (n : ℕ) (f : A → B) → UU (lsuc l1 ⊔ lsuc l2)
  where
  is-zero-coherent-equivalence :
    (f : A → B) → is-coherent-equivalence 0 f
  is-succ-coherent-equivalence :
    (n : ℕ)
    (f : A → B) (g : B → A) (H : (x : A) (y : B) → (f x ＝ y) → (x ＝ g y)) →
    ((x : A) (y : B) → is-coherent-equivalence n (H x y)) →
    is-coherent-equivalence (succ-ℕ n) f
```
