# Acyclic types

```agda
module synthetic-homotopy-theory.acyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.propositions
open import foundation.universe-levels

open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

A type `A` is said to be **acyclic** if its suspension is contractible.

## Definition

```agda
is-acyclic-Prop : {l : Level} → UU l → Prop l
is-acyclic-Prop A = is-contr-Prop (suspension A)

is-acyclic : {l : Level} → UU l → UU l
is-acyclic A = type-Prop (is-acyclic-Prop A)

is-prop-is-acyclic : {l : Level} (A : UU l) → is-prop (is-acyclic A)
is-prop-is-acyclic A = is-prop-type-Prop (is-acyclic-Prop A)
```
