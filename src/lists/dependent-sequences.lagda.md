# Dependent sequences

```agda
module lists.dependent-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

A {{#concept "dependent sequence" Agda=dependent-sequence}} of elements in a
family of types `A : ℕ → Type` is a dependent map `(n : ℕ) → A n`.

## Definition

### Dependent sequences of elements in a family of types

```agda
dependent-sequence : {l : Level} → (ℕ → UU l) → UU l
dependent-sequence B = (n : ℕ) → B n
```

### Functorial action on maps of dependent sequences

```agda
map-dependent-sequence :
  {l1 l2 : Level} {A : ℕ → UU l1} {B : ℕ → UU l2} →
  ((n : ℕ) → A n → B n) → dependent-sequence A → dependent-sequence B
map-dependent-sequence f a = map-Π f a
```
