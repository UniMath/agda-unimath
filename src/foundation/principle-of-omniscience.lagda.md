# The principle of omniscience

```agda
module foundation.principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A type `X` is said to satisfy the principle of omniscience if every decidable subtype of `X` is either inhabited or empty.

```agda
is-omniscient-Prop : {l : Level} → UU l → Prop (lsuc lzero ⊔ l)
is-omniscient-Prop X =
  Π-Prop
    ( decidable-subtype lzero X)
    ( λ P → is-decidable-Prop (trunc-Prop (type-decidable-subtype P)))

is-omniscient : {l : Level} → UU l → UU (lsuc lzero ⊔ l)
is-omniscient X = type-Prop (is-omniscient-Prop X)
```
