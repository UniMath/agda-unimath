# Isomorphisms of quasigroups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.isomorphisms-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.dependent-identifications
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications

open import group-theory.homomorphisms-quasigroups
open import group-theory.quasigroups
```

</details>

## Idea

{{#concept "isomorphisms of quasigroups" Agda=iso-Quasigroup}} are
[homomorphisms](group-theory.homomorphisms-quasigroups.md) that are also
[equivalences](foundation.equivalences.md).

## Definition

```agda
module _
  {l1 l2 : Level} (Q : Quasigroup l1) (R : Quasigroup l2)
  where

  is-iso-Quasigroup : hom-Quasigroup Q R → UU (l1 ⊔ l2)
  is-iso-Quasigroup f = is-equiv (map-hom-Quasigroup Q R f)

  is-prop-is-iso-Quasigroup :
    ( f : hom-Quasigroup Q R) → is-prop (is-iso-Quasigroup f)
  is-prop-is-iso-Quasigroup f = is-property-is-equiv (pr1 f)

  is-iso-Quasigroup-Prop : hom-Quasigroup Q R → Prop (l1 ⊔ l2)
  is-iso-Quasigroup-Prop f = (is-iso-Quasigroup f) , is-prop-is-iso-Quasigroup f

  iso-Quasigroup : UU (l1 ⊔ l2)
  iso-Quasigroup =
    Σ (hom-Quasigroup Q R) is-iso-Quasigroup
```

## Properties

### The identity isomorphism of quasigroups

```agda
id-iso-Quasigroup : {l : Level} (Q : Quasigroup l) → iso-Quasigroup Q Q
id-iso-Quasigroup Q =
  ( id-hom-Quasigroup Q) ,
  pair (pair (λ z → z) (λ x → refl)) (pair (λ z → z) (λ x → refl))
```

### Isomorphisms characterize identifications of quasigroups

```agda
iso-eq-Quasigroup :
  {l : Level} (Q R : Quasigroup l) → Q ＝ R → iso-Quasigroup Q R
iso-eq-Quasigroup Q Q refl = id-iso-Quasigroup Q

abstract
  is-torsorial-iso-Quasigroup :
    {l : Level} (Q : Quasigroup l) →
    is-torsorial (iso-Quasigroup Q)
  is-torsorial-iso-Quasigroup Q = {!   !}
```
