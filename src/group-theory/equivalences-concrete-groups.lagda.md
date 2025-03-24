# Equivalences of concrete groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.equivalences-concrete-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.universe-levels

open import group-theory.concrete-groups funext univalence truncations

open import higher-group-theory.equivalences-higher-groups funext univalence truncations
open import higher-group-theory.higher-groups funext univalence truncations
```

</details>

## Idea

An equivalence of concrete groups consists of a pointed equivalence between
their classifying types

## Definition

### Equivalences of concrete groups

```agda
equiv-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2) → UU (l1 ⊔ l2)
equiv-Concrete-Group G H =
  equiv-∞-Group (∞-group-Concrete-Group G) (∞-group-Concrete-Group H)
```

### The identity equivalence of a concrete group

```agda
id-equiv-Concrete-Group :
  {l : Level} (G : Concrete-Group l) → equiv-Concrete-Group G G
id-equiv-Concrete-Group G = id-equiv-∞-Group (∞-group-Concrete-Group G)
```

## Properties

### Characterization of equality in the type of concrete groups

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  is-torsorial-equiv-Concrete-Group :
    is-torsorial (equiv-Concrete-Group G)
  is-torsorial-equiv-Concrete-Group =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv-∞-Group (∞-group-Concrete-Group G))
      ( λ H → is-prop-is-set (type-∞-Group H))
      ( ∞-group-Concrete-Group G)
      ( id-equiv-∞-Group (∞-group-Concrete-Group G))
      ( is-set-type-Concrete-Group G)

  equiv-eq-Concrete-Group :
    (H : Concrete-Group l) → (G ＝ H) → equiv-Concrete-Group G H
  equiv-eq-Concrete-Group .G refl = id-equiv-Concrete-Group G

  is-equiv-equiv-eq-Concrete-Group :
    (H : Concrete-Group l) → is-equiv (equiv-eq-Concrete-Group H)
  is-equiv-equiv-eq-Concrete-Group =
    fundamental-theorem-id
      is-torsorial-equiv-Concrete-Group
      equiv-eq-Concrete-Group

  extensionality-Concrete-Group :
    (H : Concrete-Group l) → (G ＝ H) ≃ equiv-Concrete-Group G H
  pr1 (extensionality-Concrete-Group H) = equiv-eq-Concrete-Group H
  pr2 (extensionality-Concrete-Group H) = is-equiv-equiv-eq-Concrete-Group H

  eq-equiv-Concrete-Group :
    (H : Concrete-Group l) → equiv-Concrete-Group G H → G ＝ H
  eq-equiv-Concrete-Group H = map-inv-equiv (extensionality-Concrete-Group H)
```
