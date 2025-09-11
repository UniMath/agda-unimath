# Complements of decidable subtypes of finite types

```agda
module univalent-combinatorics.complements-decidable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import logic.complements-decidable-subtypes

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equivalences
open import univalent-combinatorics.finite-types
```

</details>

## Idea

The
{{#concept "complement" Disambiguation="of a decidable subset of a finite type" Agda=complement-decidable-subset-Finite-Type}}
of a
[decidable subtype of a finite type](univalent-combinatorics.decidable-subtypes.md)
is its [complement](logic.complements-decidable-subtypes.md) as a
[decidable subtype](foundation.decidable-subtypes.md) of a type.

## Definition

```agda
complement-subset-Finite-Type :
  {l1 l2 : Level} → (X : Finite-Type l1) → subset-Finite-Type l2 X →
  subset-Finite-Type l2 X
complement-subset-Finite-Type _ = complement-decidable-subtype

module _
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X)
  where

  type-complement-subset-Finite-Type : UU (l1 ⊔ l2)
  type-complement-subset-Finite-Type =
    type-subset-Finite-Type X (complement-subset-Finite-Type X P)

  inclusion-complement-subset-Finite-Type :
    type-complement-subset-Finite-Type → type-Finite-Type X
  inclusion-complement-subset-Finite-Type =
    inclusion-subset-Finite-Type X (complement-subset-Finite-Type X P)
```

## Properties

### The complement of a decidable subtype of a finite type is finite

```agda
module _
  {l1 l2 : Level} (X : Finite-Type l1) (P : subset-Finite-Type l2 X)
  where

  finite-type-complement-subset-Finite-Type : Finite-Type (l1 ⊔ l2)
  finite-type-complement-subset-Finite-Type =
    finite-type-subset-Finite-Type X (complement-subset-Finite-Type X P)
```

### The coproduct decomposition associated to a decidable subset of a finite type

Every decidable subtype `P ⊆ A` of a finite type `A` decomposes `A` into a
coproduct `A ≃ (P + A∖P)`.

```agda
module _
  {l1 l2 : Level} (A : Finite-Type l1) (P : subset-Finite-Type l2 A)
  where

  equiv-coproduct-decomposition-subset-Finite-Type :
    equiv-Finite-Type
      ( A)
      ( coproduct-Finite-Type
        ( finite-type-subset-Finite-Type A P)
        ( finite-type-complement-subset-Finite-Type A P))
  equiv-coproduct-decomposition-subset-Finite-Type =
    equiv-coproduct-decomposition-decidable-subtype P
```
