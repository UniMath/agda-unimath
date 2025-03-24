# The principle of omniscience

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.principle-of-omniscience
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypes funext univalence truncations
open import foundation.dependent-products-propositions funext
open import foundation.propositional-truncations funext univalence
open import foundation.universe-levels

open import foundation-core.decidable-propositions funext univalence truncations
open import foundation-core.propositions
```

</details>

## Idea

A type `X` is said to satisfy the
{{#concept "principle of omniscience" Disambiguation="type" Agda=is-omniscient}}
if every [decidable subtype](foundation.decidable-subtypes.md) of `X` is either
[inhabited](foundation.inhabited-types.md) or
[empty](foundation-core.empty-types.md).

## Definition

```agda
is-omniscient-Prop : {l : Level} → UU l → Prop (lsuc lzero ⊔ l)
is-omniscient-Prop X =
  Π-Prop
    ( decidable-subtype lzero X)
    ( λ P → is-decidable-Prop (trunc-Prop (type-decidable-subtype P)))

is-omniscient : {l : Level} → UU l → UU (lsuc lzero ⊔ l)
is-omniscient X = type-Prop (is-omniscient-Prop X)
```

## See also

- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)
