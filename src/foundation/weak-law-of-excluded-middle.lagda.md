# The weak law of excluded middle

```agda
module foundation.weak-law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import logic.de-morgan-types
```

</details>

## Idea

The
{{#concept "weak law of excluded middle" Agda=WLEM}}
asserts that any [proposition](foundation-core.propositions.md) `P` is
[De Morgan](logic.de-morgan-propositions.md).

## Definition

```
WLEM : (l : Level) → UU (lsuc l)
WLEM l = (P : Prop l) → is-de-morgan (type-Prop P)

prop-WLEM : (l : Level) → Prop (lsuc l)
prop-WLEM l = Π-Prop (Prop l) (λ P → is-de-morgan-Prop (type-Prop P))
```

## External links

- [Weak excluded middle](https://ncatlab.org/nlab/show/weak+excluded+middle) at nLab
