# The invariant basis property of rings

```agda
open import foundation.function-extensionality-axiom

module
  ring-theory.invariant-basis-property-rings
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types funext
open import foundation.universe-levels

open import ring-theory.dependent-products-rings funext
open import ring-theory.isomorphisms-rings funext
open import ring-theory.rings funext

open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Idea

A ring R is said to satisfy the invariant basis property if `R^m ≅ R^n` implies
`m = n` for any two natural numbers `m` and `n`.

## Definition

```agda
invariant-basis-property-Ring :
  {l1 : Level} → Ring l1 → UU l1
invariant-basis-property-Ring R =
  (m n : ℕ) →
  iso-Ring (Π-Ring (Fin m) (λ i → R)) (Π-Ring (Fin n) (λ i → R)) →
  Id m n
```
