# The invariant basis property of rings

```agda
module ring-theory.invariant-basis-property-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.dependent-products-rings
open import ring-theory.isomorphisms-rings
open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [ring](ring-theory.rings.md) `R` is said to satisfy the
{{#concept "invariant basis property" Disambiguation="of rings" Agda=invariant-basis-property-Ring}}
if `R^m ≅ R^n` implies `m = n` for any two
[natural numbers](elementary-number-theory.natural-numbers.md) `m` and `n`.

## Definition

```agda
invariant-basis-property-Ring :
  {l1 : Level} → Ring l1 → UU l1
invariant-basis-property-Ring R =
  (m n : ℕ) →
  iso-Ring (Π-Ring (Fin m) (λ i → R)) (Π-Ring (Fin n) (λ i → R)) →
  m ＝ n
```
