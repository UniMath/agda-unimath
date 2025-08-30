# Sequences

```agda
module lists.sequences where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types

open import lists.dependent-sequences
```

</details>

## Idea

A {{#concept "sequence" Agda=sequence}} of elements of type `A` is a map `ℕ → A`
from the [natural numbers](elementary-number-theory.natural-numbers.md) into
`A`.

For a list of number sequences from the
[On-Line Encyclopedia of Integer Sequences](https://oeis.org) {{#cite oeis}}
that are formalized in agda-unimath, see the page
[`literature.oeis`](literature.oeis.md).

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

## References

{{#bibliography}}
