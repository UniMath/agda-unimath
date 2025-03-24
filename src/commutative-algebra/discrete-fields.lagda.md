# Discrete fields

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.discrete-fields
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext univalence truncations

open import foundation.universe-levels

open import ring-theory.division-rings funext univalence truncations
```

</details>

## Idea

A **discrete field** is a commutative division ring. They are called discrete,
because only nonzero elements are assumed to be invertible.

## Definition

```agda
is-discrete-field-Commutative-Ring : {l : Level} → Commutative-Ring l → UU l
is-discrete-field-Commutative-Ring A =
  is-division-Ring (ring-Commutative-Ring A)
```
