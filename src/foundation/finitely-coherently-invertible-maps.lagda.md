# Finitely coherently invertible maps

```agda
open import foundation.function-extensionality-axiom

module foundation.finitely-coherently-invertible-maps
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types funext
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

We introduce the concept of being a
{{#concept "finitely coherently invertible map" Agda=is-finitely-coherently-invertible}}
by induction on the
[natural numbers](elementary-number-theory.natural-numbers.md). In the base
case, we say that a map `f : A → B` is a
{{#concept "`0`-coherently invertible map" Agda=is-finitely-coherently-invertible}}
if it comes equipped with a map `g : B → A`. Recursively, we say that a map
`f : A → B` is an
{{#concept "`n + 1`-coherently invertible map" Agda=is-finitely-coherently-invertible}}
if it comes equipped with map `g : B → A` and a family of maps

```text
  r x y : (f x ＝ y) → (x ＝ g y)
```

indexed by `x : A` and `y : B`, such that each `r x y` is `n`-coherently
invertible.

A `1`-coherently invertible map `f : A → B` is therefore equivalently described
as a map equipped with an inverse `g : B → A` which is simultaneously a
[retraction](foundation-core.retractions.md) and a
[section](foundation-core.sections.md) of `f`. In other words, a `1`-coherently
invertible map is just an [invertible map](foundation-core.invertible-maps.md).

A `2`-coherently invertible map `f : A → B` comes equipped with `g : B → A` and
for each `x : A` and `y : B` two maps

```text
  r : (f x ＝ y) → (x ＝ g y)
  s : (x ＝ g y) → (f x ＝ y)
```

and for each `p : f x ＝ y` and `q : x ＝ g y` a map

```text
  t p q : (r p ＝ q) → (p ＝ s q)
  u p q : (p ＝ s q) → (r p ＝ q).
```

This data is equivalent to the data of

```text
  r : (x : A) → g (f x) ＝ x
  s : (y : B) → f (g y) ＝ y
  t : (x : A) → ap f (r x) ＝ s (f x)
  u : (y : B) → ap g (s y) ＝ r (f y).
```

The condition of being a `n`-coherently invertible map is not a
[proposition](foundation-core.propositions.md) for any `n`. In fact, for `n ≥ 1`
the type of all `n`-coherently invertible maps in a universe `𝒰` is equivalent
to the type of maps `sphere (n + 1) → 𝒰` of `n + 1`-spheres in the universe `𝒰`.

## Definitions

### The predicate of being an `n`-coherently invertible map

```agda
data
  is-finitely-coherently-invertible
    {l1 l2 : Level} {A : UU l1} {B : UU l2} :
    (n : ℕ) (f : A → B) → UU (l1 ⊔ l2)
  where
  is-zero-coherently-invertible :
    (f : A → B) → (B → A) → is-finitely-coherently-invertible 0 f
  is-succ-coherently-invertible :
    (n : ℕ)
    (f : A → B) (g : B → A) (H : (x : A) (y : B) → (f x ＝ y) → (x ＝ g y)) →
    ((x : A) (y : B) → is-finitely-coherently-invertible n (H x y)) →
    is-finitely-coherently-invertible (succ-ℕ n) f
```
