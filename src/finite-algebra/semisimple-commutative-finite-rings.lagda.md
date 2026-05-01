# Semisimple commutative finite rings

```agda
module finite-algebra.semisimple-commutative-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-algebra.commutative-finite-rings
open import finite-algebra.dependent-products-commutative-finite-rings
open import finite-algebra.finite-fields
open import finite-algebra.homomorphisms-commutative-finite-rings

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "semisimple commutative finite ring" Agda=Semisimple-Finite-Commutative-Ring}}
is a [commutative finite ring](finite-algebra.commutative-finite-rings.md) which
is merely equivalent to an iterated cartesian product of
[finite fields](finite-algebra.finite-fields.md).

## Definitions

### Semisimple commutative finite rings

```agda
is-semisimple-Finite-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Finite-Commutative-Ring l1 →
  UU (l1 ⊔ lsuc l2)
is-semisimple-Finite-Commutative-Ring l2 R =
  exists
    ( ℕ)
    ( λ n →
      ∃ ( Fin n → Finite-Field l2)
        ( λ A →
          trunc-Prop
            ( hom-Finite-Commutative-Ring
              ( R)
              ( Π-Finite-Commutative-Ring
                ( Fin n , is-finite-Fin n)
                ( commutative-finite-ring-Finite-Field ∘ A)))))

Semisimple-Finite-Commutative-Ring :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Semisimple-Finite-Commutative-Ring l1 l2 =
  Σ (Finite-Commutative-Ring l1) (is-semisimple-Finite-Commutative-Ring l2)

module _
  {l1 l2 : Level} (A : Semisimple-Finite-Commutative-Ring l1 l2)
  where

  commutative-finite-ring-Semisimple-Finite-Commutative-Ring :
    Finite-Commutative-Ring l1
  commutative-finite-ring-Semisimple-Finite-Commutative-Ring = pr1 A
```

## Properties

### The number of ways to equip a finite type with the structure of a semisimple commutative ring is finite

```agda
module _
  {l1 : Level}
  (l2 : Level)
  (X : Finite-Type l1)
  where

  structure-semisimple-commutative-ring-Finite-Type :
    UU (l1 ⊔ lsuc l2)
  structure-semisimple-commutative-ring-Finite-Type =
    Σ ( structure-commutative-ring-Finite-Type X)
      ( λ r →
        is-semisimple-Finite-Commutative-Ring
          ( l2)
          ( finite-commutative-ring-structure-commutative-ring-Finite-Type X r))

  finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-Finite-Type :
    structure-semisimple-commutative-ring-Finite-Type →
    Semisimple-Finite-Commutative-Ring l1 l2
  finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-Finite-Type =
    map-Σ-map-base
      ( finite-commutative-ring-structure-commutative-ring-Finite-Type X)
      ( is-semisimple-Finite-Commutative-Ring l2)
```
