# π-finite types

```agda
{-# OPTIONS --guardedness #-}

module univalent-combinatorics.pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.conjunction
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-function-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.finitely-truncated-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.retracts-of-finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.truncated-pi-finite-types
open import univalent-combinatorics.unbounded-pi-finite-types
open import univalent-combinatorics.untruncated-pi-finite-types
```

</details>

## Idea

A type is
{{#concept "π-finite" Disambiguation="type" Agda=is-π-finite Agda=π-Finite-Type}}
if it has
[finitely many connected components](univalent-combinatorics.finitely-many-connected-components.md),
all of its [homotopy groups](synthetic-homotopy-theory.homotopy-groups.md) are
[finite](univalent-combinatorics.finite-types.md), and it is $n$-truncated for
some $n$ {{#cite Anel24}}. However, formally we define a π-finite type to be a
[finitely truncated type](foundation.finitely-truncated-types.md) that is
[unbounded π-finite](univalent-combinatorics.unbounded-pi-finite-types.md).

## Definitions

### The π-finiteness predicate

```agda
is-π-finite-Prop : {l : Level} → UU l → Prop l
is-π-finite-Prop A =
  is-finitely-trunc-Prop A ∧ is-unbounded-π-finite-Prop' A

is-π-finite : {l : Level} → UU l → UU l
is-π-finite A = type-Prop (is-π-finite-Prop A)

is-prop-is-π-finite :
  {l : Level} {A : UU l} → is-prop (is-π-finite A)
is-prop-is-π-finite {A = A} =
  is-prop-type-Prop (is-π-finite-Prop A)

module _
  {l : Level} {A : UU l} (H : is-π-finite A)
  where

  is-finitely-trunc-is-π-finite : is-finitely-trunc A
  is-finitely-trunc-is-π-finite = pr1 H

  is-unbounded-π-finite-is-π-finite : is-unbounded-π-finite' A
  is-unbounded-π-finite-is-π-finite = pr2 H

  has-finitely-many-connected-components-is-π-finite :
    has-finitely-many-connected-components A
  has-finitely-many-connected-components-is-π-finite =
    has-finitely-many-connected-components-is-untruncated-π-finite 0
      ( is-unbounded-π-finite-is-π-finite 0)
```

### The subuniverse of π-finite types

```agda
π-Finite-Type : (l : Level) → UU (lsuc l)
π-Finite-Type l = Σ (UU l) (is-π-finite)

module _
  {l : Level} (A : π-Finite-Type l)
  where

  type-π-Finite-Type : UU l
  type-π-Finite-Type = pr1 A

  is-π-finite-type-π-Finite-Type : is-π-finite type-π-Finite-Type
  is-π-finite-type-π-Finite-Type = pr2 A

  is-finitely-trunc-type-π-Finite-Type :
    is-finitely-trunc type-π-Finite-Type
  is-finitely-trunc-type-π-Finite-Type =
    is-finitely-trunc-is-π-finite is-π-finite-type-π-Finite-Type

  is-unbounded-π-finite-type-π-Finite-Type :
    is-unbounded-π-finite' type-π-Finite-Type
  is-unbounded-π-finite-type-π-Finite-Type =
    is-unbounded-π-finite-is-π-finite is-π-finite-type-π-Finite-Type

  has-finitely-many-connected-components-type-π-Finite-Type :
    has-finitely-many-connected-components type-π-Finite-Type
  has-finitely-many-connected-components-type-π-Finite-Type =
    has-finitely-many-connected-components-is-π-finite
      is-π-finite-type-π-Finite-Type
```

## Properties

### Truncated π-finite types are π-finite

```agda
is-π-finite-is-truncated-π-finite :
  {l : Level} (n : ℕ) {A : UU l} → is-truncated-π-finite n A → is-π-finite A
is-π-finite-is-truncated-π-finite n H =
  ( intro-exists (truncation-level-ℕ n) (is-trunc-is-truncated-π-finite n H) ,
    is-unbounded-π-finite-is-truncated-π-finite' n H)
```

### π-finite types are closed under retracts

```agda
is-π-finite-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → is-π-finite B → is-π-finite A
pr1 (is-π-finite-retract R H) =
  is-finitely-trunc-retract-of R (is-finitely-trunc-is-π-finite H)
pr2 (is-π-finite-retract R H) n =
  is-untruncated-π-finite-retract n R (is-unbounded-π-finite-is-π-finite H n)
```

### π-finite types are closed under equivalences

```agda
is-π-finite-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-π-finite B → is-π-finite A
is-π-finite-equiv e =
  is-π-finite-retract (retract-equiv e)

is-π-finite-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-π-finite A → is-π-finite B
is-π-finite-equiv' e =
  is-π-finite-retract (retract-inv-equiv e)
```

### Empty types are π-finite

```agda
is-π-finite-empty : is-π-finite empty
is-π-finite-empty =
  is-π-finite-is-truncated-π-finite 0 (is-truncated-π-finite-empty 0)

empty-π-Finite-Type : π-Finite-Type lzero
empty-π-Finite-Type = (empty , is-π-finite-empty)

is-π-finite-is-empty :
  {l : Level} {A : UU l} → is-empty A → is-π-finite A
is-π-finite-is-empty H =
  is-π-finite-is-truncated-π-finite 0 (is-truncated-π-finite-is-empty 0 H)
```

### Contractible types are π-finite

```agda
is-π-finite-is-contr :
  {l : Level} {A : UU l} → is-contr A → is-π-finite A
is-π-finite-is-contr H =
  is-π-finite-is-truncated-π-finite 0 (is-truncated-π-finite-is-contr 0 H)

is-π-finite-unit : is-π-finite unit
is-π-finite-unit =
  is-π-finite-is-contr is-contr-unit

unit-π-Finite-Type : π-Finite-Type lzero
unit-π-Finite-Type =
  ( unit , is-π-finite-unit)
```

### Coproducts of π-finite types are π-finite

```agda
is-π-finite-coproduct :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-π-finite A → is-π-finite B →
  is-π-finite (A + B)
is-π-finite-coproduct hA hB =
  ( ( is-finitely-trunc-coproduct
      ( is-finitely-trunc-is-π-finite hA)
      ( is-finitely-trunc-is-π-finite hB)) ,
    ( λ n →
      is-untruncated-π-finite-coproduct n
        ( is-unbounded-π-finite-is-π-finite hA n)
        ( is-unbounded-π-finite-is-π-finite hB n)))

coproduct-π-Finite-Type :
  {l1 l2 : Level} →
  π-Finite-Type l1 → π-Finite-Type l2 → π-Finite-Type (l1 ⊔ l2)
pr1 (coproduct-π-Finite-Type A B) =
  type-π-Finite-Type A + type-π-Finite-Type B
pr2 (coproduct-π-Finite-Type A B) =
  is-π-finite-coproduct
    ( is-π-finite-type-π-Finite-Type A)
    ( is-π-finite-type-π-Finite-Type B)
```

### `Maybe A` of any π-finite type `A` is π-finite

```agda
is-π-finite-Maybe :
  {l : Level} {A : UU l} → is-π-finite A → is-π-finite (Maybe A)
is-π-finite-Maybe H = is-π-finite-coproduct H (is-π-finite-unit)

Maybe-π-Finite-Type :
  {l : Level} → π-Finite-Type l → π-Finite-Type l
Maybe-π-Finite-Type (A , H) = (Maybe A , is-π-finite-Maybe H)
```

### Any standard finite type is π-finite

```agda
is-π-finite-Fin : (n : ℕ) → is-π-finite (Fin n)
is-π-finite-Fin n =
  is-π-finite-is-truncated-π-finite 0 (is-truncated-π-finite-Fin 0 n)

Fin-π-Finite-Type : (n : ℕ) → π-Finite-Type lzero
Fin-π-Finite-Type n = (Fin n , is-π-finite-Fin n)
```

### Any type equipped with a counting is π-finite

```agda
is-π-finite-count : {l : Level} {A : UU l} → count A → is-π-finite A
is-π-finite-count (n , e) = is-π-finite-equiv' e (is-π-finite-Fin n)
```

### Any finite type is π-finite

```agda
is-π-finite-is-finite :
  {l : Level} {A : UU l} → is-finite A → is-π-finite A
is-π-finite-is-finite {A = A} H =
  apply-universal-property-trunc-Prop H
    ( is-π-finite-Prop A)
    ( is-π-finite-count)

π-finite-Finite-Type : {l : Level} → Finite-Type l → π-Finite-Type l
π-finite-Finite-Type A =
  ( type-Finite-Type A , is-π-finite-is-finite (is-finite-type-Finite-Type A))
```

### π-finite sets are finite

```agda
is-finite-is-π-finite :
  {l : Level} {A : UU l} → is-set A → is-π-finite A → is-finite A
is-finite-is-π-finite H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (_ , H))
    ( has-finitely-many-connected-components-is-π-finite K)
```

## References

{{#bibliography}}

## See also

- [Unbounded π-finite types](univalent-combinatorics.unbounded-pi-finite-types.md)

## External links

- [pi-finite type](https://ncatlab.org/nlab/show/pi-finite+type) at $n$Lab
