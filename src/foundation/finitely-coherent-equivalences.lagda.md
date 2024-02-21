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

The condition of being a
{{#concept "finitely coherent equivalence" Agda=is-finitely-coherent-equivalence}}
is introduced by induction on the
[natural numbers](elementary-number-theory.natural-numbers.md). In the base
case, we say that any map `f : A → B` is a
{{#concept "`0`-coherent equivalence" Agda=is-finitely-coherent-equivalence}}.
Recursively, we say that a map `f : A → B` is an
{{#concept "`n + 1`-coherent equivalence" Agda=is-finitely-coherent-equivalence}}
if it comes equipped with a map `g : B → A` and a family of maps

```text
  r x y : (f x ＝ y) → (x ＝ g y)
```

indexed by `x : A` and `y : B`, such that each `r x y` is an `n`-coherent
equivalence.

By the equivalence of [retracting homotopies](foundation-core.retractions.md)
and
[transposition operations of identifications](foundation.transposition-identifications-along-retractions.md)
it therefore follows that a `1`-coherent equivalence is equivalently described
as a map equipped with a retraction. A `2`-coherent equivalence is a map
`f : A → B` equipped with `g : B → A` and for each `x : A` and `y : B` a map
`r x y : (f x ＝ y) → (x ＝ g y)`, equipped with

```text
  s x y : (x ＝ g y) → (f x ＝ y)
```

and for each `p : f x ＝ y` and `q : x ＝ g y` a map

```text
  t p q : (r x y p ＝ q) → (p ＝ s x y q).
```

This data is equivalent to the data of a
[coherently invertible map](foundation-core.coherently-invertible-maps.md)

```text
  r : (x : A) → g (f x) ＝ x
  s : (y : B) → f (g y) ＝ y
  t : (x : A) → ap f (r x) ＝ s (f x).
```

The condition of being an `n`-coherent equivalence is a
[proposition](foundation-core.propositions.md) for each `n ≥ 2`, and this
proposition is equivalent to being an equivalence.

## Definitions

### The predicate of being an `n`-coherent equivalence

```agda
data
  is-finitely-coherent-equivalence
    {l1 l2 : Level} {A : UU l1} {B : UU l2} :
    (n : ℕ) (f : A → B) → UU (l1 ⊔ l2)
  where
  is-zero-coherent-equivalence :
    (f : A → B) → is-finitely-coherent-equivalence 0 f
  is-succ-coherent-equivalence :
    (n : ℕ)
    (f : A → B) (g : B → A) (H : (x : A) (y : B) → (f x ＝ y) → (x ＝ g y)) →
    ((x : A) (y : B) → is-finitely-coherent-equivalence n (H x y)) →
    is-finitely-coherent-equivalence (succ-ℕ n) f
```
