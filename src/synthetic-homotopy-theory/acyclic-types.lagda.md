# Acyclic types

```agda
module synthetic-homotopy-theory.acyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.equivalences
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.functoriality-suspensions
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

A type `A` is said to be **acyclic** if its
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[contractible](foundation.contractible-types.md).

## Definition

```agda
is-acyclic-Prop : {l : Level} → UU l → Prop l
is-acyclic-Prop A = is-contr-Prop (suspension A)

is-acyclic : {l : Level} → UU l → UU l
is-acyclic A = type-Prop (is-acyclic-Prop A)

is-prop-is-acyclic : {l : Level} (A : UU l) → is-prop (is-acyclic A)
is-prop-is-acyclic A = is-prop-type-Prop (is-acyclic-Prop A)
```

## Properties

### Being acyclic is invariant under equivalence

```agda
is-acyclic-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-acyclic B → is-acyclic A
is-acyclic-equiv {B = B} e ac =
  is-contr-equiv (suspension B) (equiv-suspension e) ac

is-acyclic-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-acyclic A → is-acyclic B
is-acyclic-equiv' e = is-acyclic-equiv (inv-equiv e)
```

### Acyclic types are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-acyclic-retract-of : A retract-of B → is-acyclic B → is-acyclic A
  is-acyclic-retract-of R ac =
    is-contr-retract-of (suspension B) (retract-of-suspension-retract-of R) ac
```

### Contractible types are acyclic

```agda
is-acyclic-is-contr : {l : Level} (A : UU l) → is-contr A → is-acyclic A
is-acyclic-is-contr A = is-contr-suspension-is-contr

is-acyclic-unit : is-acyclic unit
is-acyclic-unit = is-acyclic-is-contr unit is-contr-unit
```

### Acyclic types are inhabited

> TODO

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
