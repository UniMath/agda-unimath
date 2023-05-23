# Finite fields

```agda
module univalent-combinatorics.finite-fields where
```

<details><summary>Imports</summary>

```agda
open import univalent-combinatorics.commutative-finite-rings

open import foundation.universe-levels
open import foundation.dependent-pair-types

open import ring-theory.division-rings
```

</details>

## Idea

A **discrete field** is a commutative division ring. They are called discrete,
because only nonzero elements are assumed to be invertible.

## Definition

```agda
is-finite-field-Commutative-Ring-𝔽 : {l : Level} → Commutative-Ring-𝔽 l → UU l
is-finite-field-Commutative-Ring-𝔽 A =
  is-division-Ring (ring-Commutative-Ring-𝔽 A)

Field-𝔽 : (l : Level) → UU (lsuc l)
Field-𝔽 l =
  Σ (Commutative-Ring-𝔽 l) (λ A → is-finite-field-Commutative-Ring-𝔽 A)
```
