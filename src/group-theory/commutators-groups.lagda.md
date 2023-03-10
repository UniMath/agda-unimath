# Commutators of elements in groups

```agda
module group-theory.commutators-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.group-solver
open import group-theory.groups
```

</details>

## Idea

A commutator gives an indication of the extent to which a group multiplication fails to be commutative.

The commutator of two elements, g and h, of a group G, is the element `[g, h] = (gh)(hg)⁻¹`.

https://en.wikipedia.org/wiki/Commutator#Group_theory

## Definition

```agda
module _
  {l : Level} (G : Group l)
  where

  commutator-Group : type-Group G → type-Group G → type-Group G
  commutator-Group x y = right-div-Group G (mul-Group G x y) (mul-Group G y x)
```

## Properties

### The commutator of x and y is unit if and only x and y commutes

```agda
module _
  {l : Level} (G : Group l)
  where

  is-unit-commutator-commute-Group :
    (x y : type-Group G) →
    commute-Group G x y → is-unit-Group G (commutator-Group G x y)
  is-unit-commutator-commute-Group x y H =
    is-unit-right-div-eq-Group G H

  commute-is-unit-commutator-Group :
    (x y : type-Group G) →
    is-unit-Group G (commutator-Group G x y) → commute-Group G x y
  commute-is-unit-commutator-Group x y H =
    eq-is-unit-right-div-Group G H
```

### The inverse of the `[x,y]` is `[y,x]`

```agda
  inv-commutator-Group : ∀ x y → inv-Group G (commutator-Group G x y) ＝ commutator-Group G y x
  inv-commutator-Group x y = inv-right-div-Group G (mul-Group G x y) (mul-Group G y x)
```

### Demonstration of the group solver

We first introduce some shorter names to make the proofs less verbose

```agda
module _
  {l : Level} (G : Group l)
  where

  private
    _*_ = mul-Group G
    infixl 30 _*_
    _⁻¹ = inv-Group G
    infix 40 _⁻¹
    unit = unit-Group G

    _*'_ : ∀ {n} → GroupSyntax n → GroupSyntax n → GroupSyntax n
    _*'_ = gMul
    infixl 20 _*'_

  gCommutator : ∀ {n} → GroupSyntax n → GroupSyntax n → GroupSyntax n
  gCommutator x y = x *' y *' gInv (y *' x)

  inv-Commutator-law' : ∀ x y → inv-Group G (commutator-Group G x y) ＝ commutator-Group G y x
  inv-Commutator-law' x y =
    equational-reasoning
      ( commutator-Group G x y) ⁻¹
        ＝ y * x * y ⁻¹ * x ⁻¹       by simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → gInv (gCommutator x y))
        ＝ commutator-Group G y x    by inv (simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → gCommutator y x))

  inv-Commutator-law'' : ∀ x y → inv-Group G (commutator-Group G x y) ＝ commutator-Group G y x
  inv-Commutator-law'' x y =
    simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → gInv (gCommutator x y)) ∙
      inv (simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → gCommutator y x))

  commutes-when-commutor-is-unit' :
    ∀ x y → (commutator-Group G x y ＝ unit-Group G) → mul-Group G x y ＝ mul-Group G y x
  commutes-when-commutor-is-unit' x y comm-unit =
    equational-reasoning
      x * y ＝ commutator-Group G x y * y * x    by inv (simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → (gCommutator x y *' y *' x)))
            ＝ unit * y * x                      by ap (λ z → z * y * x) comm-unit
            ＝ y * x                             by simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → (gUnit *' y *' x))

  commutor-is-unit-when-commutes' :
    ∀ x y → (mul-Group G x y ＝ mul-Group G y x) → commutator-Group G x y ＝ unit-Group G
  commutor-is-unit-when-commutes' x y commutes =
    equational-reasoning
      x * y * (y * x) ⁻¹ ＝ y * x * (y * x) ⁻¹    by ap (λ z → z * (y * x) ⁻¹) commutes
                         ＝ unit                  by simplifyExpr G (x ∷ y ∷ empty-vec) (λ x y → (y *' x *' gInv (y *' x)))
```
