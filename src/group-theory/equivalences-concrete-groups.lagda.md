# Equivalences of concrete groups

```agda
module group-theory.equivalences-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.equivalences-higher-groups
open import group-theory.higher-groups
```

</details>

## Idea

An equivalence of concrete groups consists of a pointed equivalence between their classifying types

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

  is-contr-total-equiv-Concrete-Group :
    is-contr (Σ (Concrete-Group l) (equiv-Concrete-Group G))
  is-contr-total-equiv-Concrete-Group =
    is-contr-total-Eq-subtype
      ( is-contr-total-equiv-∞-Group (∞-group-Concrete-Group G))
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
      is-contr-total-equiv-Concrete-Group
      equiv-eq-Concrete-Group

  extensionality-Concrete-Group :
    (H : Concrete-Group l) → (G ＝ H) ≃ equiv-Concrete-Group G H
  pr1 (extensionality-Concrete-Group H) = equiv-eq-Concrete-Group H
  pr2 (extensionality-Concrete-Group H) = is-equiv-equiv-eq-Concrete-Group H

  eq-equiv-Concrete-Group :
    (H : Concrete-Group l) → equiv-Concrete-Group G H → G ＝ H
  eq-equiv-Concrete-Group H = map-inv-equiv (extensionality-Concrete-Group H)
```
