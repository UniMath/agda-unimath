# `k`-acyclic types

```agda
module synthetic-homotopy-theory.truncated-acyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.equivalences
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.functoriality-suspensions
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

A type `A` is said to be **`k`-acyclic** if its
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`k`-connected](foundation.connected-types.md).

## Definition

```agda
module _
  {l : Level} (k : 𝕋) (A : UU l)
  where

  is-truncated-acyclic-Prop : Prop l
  is-truncated-acyclic-Prop = is-connected-Prop k (suspension A)

  is-truncated-acyclic : UU l
  is-truncated-acyclic = type-Prop is-truncated-acyclic-Prop

  is-prop-is-truncated-acyclic : is-prop is-truncated-acyclic
  is-prop-is-truncated-acyclic = is-prop-type-Prop is-truncated-acyclic-Prop
```

## Properties

### Being `k`-acyclic is invariant under equivalence

```agda
is-truncated-acyclic-equiv :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} →
  A ≃ B → is-truncated-acyclic k B → is-truncated-acyclic k A
is-truncated-acyclic-equiv {k = k} {B = B} e ac =
  is-connected-equiv (equiv-suspension e) ac

is-truncated-acyclic-equiv' :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} →
  A ≃ B → is-truncated-acyclic k A → is-truncated-acyclic k B
is-truncated-acyclic-equiv' e = is-truncated-acyclic-equiv (inv-equiv e)
```

### `k`-acyclic types are closed under retracts

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-truncated-acyclic-retract-of :
    A retract-of B →
    is-truncated-acyclic k B →
    is-truncated-acyclic k A
  is-truncated-acyclic-retract-of R ac =
    is-connected-retract-of
      ( retract-of-suspension-retract-of R)
      ( ac)
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
