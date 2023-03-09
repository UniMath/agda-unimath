# Uncountable sets

```agda
module set-theory.uncountable-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import set-theory.countable-sets
```

</details>

## Definition

```agda
is-uncountable-Prop : {l : Level} → Set l → Prop l
is-uncountable-Prop X = neg-Prop (is-countable-Prop X)

is-uncountable : {l : Level} → Set l → UU l
is-uncountable X = type-Prop (is-uncountable-Prop X)

is-prop-is-uncountable : {l : Level} (X : Set l) → is-prop (is-uncountable X)
is-prop-is-uncountable X = is-prop-type-Prop (is-uncountable-Prop X)
```
