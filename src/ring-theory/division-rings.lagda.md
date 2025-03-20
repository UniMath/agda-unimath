# Division rings

```agda
open import foundation.function-extensionality-axiom

module
  ring-theory.division-rings
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.negated-equality funext
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings funext
open import ring-theory.rings funext
open import ring-theory.trivial-rings funext
```

</details>

## Idea

Division rings are nontrivial rings in which all nonzero elements are
invertible.

## Definition

```agda
is-division-Ring :
  { l : Level} → Ring l → UU l
is-division-Ring R =
  (is-nontrivial-Ring R) ×
  ((x : type-Ring R) → zero-Ring R ≠ x → is-invertible-element-Ring R x)
```
