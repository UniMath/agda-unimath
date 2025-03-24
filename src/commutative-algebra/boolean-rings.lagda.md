# Boolean rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.boolean-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import ring-theory.idempotent-elements-rings funext univalence truncations
```

</details>

## Idea

A **boolean ring** is a commutative ring in which every element is idempotent.

## Definition

```agda
is-boolean-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → UU l
is-boolean-Commutative-Ring A =
  (x : type-Commutative-Ring A) →
  is-idempotent-element-Ring (ring-Commutative-Ring A) x

Boolean-Ring : (l : Level) → UU (lsuc l)
Boolean-Ring l = Σ (Commutative-Ring l) is-boolean-Commutative-Ring

module _
  {l : Level} (A : Boolean-Ring l)
  where

  commutative-ring-Boolean-Ring : Commutative-Ring l
  commutative-ring-Boolean-Ring = pr1 A
```
