# Uncountable sets

```agda
module set-theory.uncountable-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import set-theory.countable-sets
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
