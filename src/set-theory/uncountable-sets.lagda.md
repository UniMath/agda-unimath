# Uncountable sets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module set-theory.uncountable-sets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.negation funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels

open import set-theory.countable-sets funext univalence truncations
```

</details>

## Idea

A [set](foundation-core.sets.md) `X` is
{{#concept "uncountable" Disambiguation="set" Agda=is-uncountable WD="uncountable set" WDID=Q1128796}}
if `X` is not [empty](foundation-core.empty-types.md) and there is
[no](foundation-core.negation.md) [surjection](foundation.surjective-maps.md)
`ℕ ↠ X`. In other words, if `X` is not
[countable](set-theory.countable-sets.md).

## Definition

```agda
is-uncountable-Prop : {l : Level} → Set l → Prop l
is-uncountable-Prop X = neg-Prop (is-countable-Prop X)

is-uncountable : {l : Level} → Set l → UU l
is-uncountable X = type-Prop (is-uncountable-Prop X)

is-prop-is-uncountable : {l : Level} (X : Set l) → is-prop (is-uncountable X)
is-prop-is-uncountable X = is-prop-type-Prop (is-uncountable-Prop X)
```

## External links

- [Uncountable set](https://en.wikipedia.org/wiki/Uncountable_set) at Wikipedia
