# Finitely enumerable types

```agda
module univalent-combinatorics.finitely-enumerable-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.surjective-maps
```

</details>

## Idea

A type `X` is
{{#concept "finitely enumerable" disambiguation="type" Agda=finitely-enumerable-type}}
if there is an `n : ℕ` and a [surjection](foundation.surjective-maps.md) from
`Fin n → X + 1`.

## Definition

```agda
module _
  {l : Level} (X : UU l)
  where

  finite-enumeration : UU l
  finite-enumeration = Σ ℕ (λ n → Fin n ↠ Maybe X)

  is-finitely-enumerable-prop : Prop l
  is-finitely-enumerable-prop = trunc-Prop finite-enumeration

  is-finitely-enumerable : UU l
  is-finitely-enumerable = type-Prop is-finitely-enumerable-prop
```

## Properties

### Finitely enumerable types with decidable equality are finite

```agda
module _
  {l : Level} {X : UU l} (D : has-decidable-equality X)
  where

  count-discrete-finite-enumeration : finite-enumeration X → count X
  count-discrete-finite-enumeration (n , Fin-n⇸X) =
    count-left-summand
      ( count-surjection-has-decidable-equality
        ( n)
        ( has-decidable-equality-coproduct D has-decidable-equality-unit)
        ( Fin-n⇸X))

  is-finite-discrete-finite-enumeration : finite-enumeration X → is-finite X
  is-finite-discrete-finite-enumeration F =
    is-finite-count (count-discrete-finite-enumeration F)

  is-finite-discrete-is-finitely-enumerable :
    is-finitely-enumerable X → is-finite X
  is-finite-discrete-is-finitely-enumerable =
    rec-trunc-Prop (is-finite-Prop X) is-finite-discrete-finite-enumeration
```

## See also

- [Surjective maps between finite types](univalent-combinatorics.surjective-maps.md)
