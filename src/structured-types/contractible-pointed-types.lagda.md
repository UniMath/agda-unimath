# Contractible pointed types

```agda
module structured-types.contractible-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.propositions
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "contractible pointed type" Agda=is-contr-Pointed-Type}} is a
[pointed type](structured-types.pointed-types.md) that is
[contractible](foundation-core.contractible-types.md).

## Definition

```agda
is-contr-pointed-type-Prop : {l : Level} → Pointed-Type l → Prop l
is-contr-pointed-type-Prop A = is-contr-Prop (type-Pointed-Type A)

is-contr-Pointed-Type : {l : Level} → Pointed-Type l → UU l
is-contr-Pointed-Type A = type-Prop (is-contr-pointed-type-Prop A)

is-prop-is-contr-Pointed-Type :
  {l : Level} (A : Pointed-Type l) → is-prop (is-contr-Pointed-Type A)
is-prop-is-contr-Pointed-Type A =
  is-prop-type-Prop (is-contr-pointed-type-Prop A)
```
