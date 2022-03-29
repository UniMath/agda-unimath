# Groups of order 2

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module finite-group-theory.groups-of-order-2 where

open import elementary-number-theory.groups-of-modular-arithmetic

open import finite-group-theory.finite-groups

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.symmetric-groups

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.finite-types

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

## Idea

The type of groups of order 2 is contractible

## Definitions

### The type of groups of order 2

```agda
Group-of-Order-2 : (l : Level) → UU (lsuc l)
Group-of-Order-2 l = Group-of-Order l 2

module _
  {l : Level} (G : Group-of-Order-2 l)
  where

  group-Group-of-Order-2 : Group l
  group-Group-of-Order-2 = pr1 G

  type-Group-of-Order-2 : UU l
  type-Group-of-Order-2 = type-Group group-Group-of-Order-2

  is-set-type-Group-of-Order-2 : is-set type-Group-of-Order-2
  is-set-type-Group-of-Order-2 = is-set-type-Group group-Group-of-Order-2

  mul-Group-of-Order-2 : (x y : type-Group-of-Order-2) → type-Group-of-Order-2
  mul-Group-of-Order-2 = mul-Group group-Group-of-Order-2

  unit-Group-of-Order-2 : type-Group-of-Order-2
  unit-Group-of-Order-2 = unit-Group group-Group-of-Order-2

  has-cardinality-2-Group-of-Order-2 :
    has-cardinality 2 (type-Group-of-Order-2)
  has-cardinality-2-Group-of-Order-2 = pr2 G

  2-element-type-Group-of-Order-2 : 2-Element-Type l
  pr1 2-element-type-Group-of-Order-2 = type-Group-of-Order-2
  pr2 2-element-type-Group-of-Order-2 = has-cardinality-2-Group-of-Order-2
```

### The group ℤ/2 of order 2

```agda
ℤ-Mod-2-Group-of-Order-2 : Group-of-Order-2 lzero
pr1 ℤ-Mod-2-Group-of-Order-2 = ℤ-Mod-Group 2
pr2 ℤ-Mod-2-Group-of-Order-2 = refl-mere-equiv (Fin 2)
```

### The permutation group S₂ of order 2

```agda
symmetric-Group-of-Order-2 : (l : Level) → Group-of-Order-2 l
pr1 (symmetric-Group-of-Order-2 l) = symmetric-Group (pair (raise-Fin l 2) {!!})
pr2 (symmetric-Group-of-Order-2 l) = {!!}
--  unit-trunc-Prop (inv-equiv equiv-ev-zero-aut-Fin-two-ℕ)
```

## Properties

### The type of groups of order 2 is contractible

```agda
is-contr-Group-of-Order-2 : (l : Level) → is-contr (Group-of-Order-2 l)
is-contr-Group-of-Order-2 l = {!!}
```
