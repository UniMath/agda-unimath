# Sequences

```agda
module foundation.sequences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-sequences
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

A **sequence** of elements in a type `A` is a map `ℕ → A`.

## Definition

### Sequences of elements of a type

```agda
sequence : {l : Level} → UU l → UU l
sequence A = dependent-sequence (λ _ → A)
```

### Functorial action on maps of sequences

```agda
map-sequence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → sequence A → sequence B
map-sequence f a = f ∘ a
```
