# Dependent products of unital algebras over commutative rings

```agda
module commutative-algebra.dependent-products-unital-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.dependent-products-algebras-commutative-rings
open import commutative-algebra.unital-algebras-commutative-rings

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.unital-binary-operations
open import foundation.universe-levels
```

</details>

## Idea

Given a [commutative ring](commutative-algebra.commutative-rings.md) `R` and a
family of
[unital algebras](commutative-algebra.unital-algebras-commutative-rings.md) `Aᵢ`
over `R` indexed by `i : I`, the dependent product `Π (i : I) Aᵢ` is a unital
algebra over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (I : UU l2)
  (A : I → unital-algebra-Commutative-Ring l3 R)
  where

  algebra-Π-unital-algebra-Commutative-Ring :
    algebra-Commutative-Ring (l2 ⊔ l3) R
  algebra-Π-unital-algebra-Commutative-Ring =
    Π-algebra-Commutative-Ring R
      ( I)
      ( λ i → algebra-unital-algebra-Commutative-Ring R (A i))

  type-Π-unital-algebra-Commutative-Ring : UU (l2 ⊔ l3)
  type-Π-unital-algebra-Commutative-Ring =
    (i : I) → type-unital-algebra-Commutative-Ring R (A i)

  one-Π-unital-algebra-Commutative-Ring : type-Π-unital-algebra-Commutative-Ring
  one-Π-unital-algebra-Commutative-Ring i =
    one-unital-algebra-Commutative-Ring R (A i)

  mul-Π-unital-algebra-Commutative-Ring :
    type-Π-unital-algebra-Commutative-Ring →
    type-Π-unital-algebra-Commutative-Ring →
    type-Π-unital-algebra-Commutative-Ring
  mul-Π-unital-algebra-Commutative-Ring =
    mul-algebra-Commutative-Ring R algebra-Π-unital-algebra-Commutative-Ring

  abstract
    left-unit-law-mul-Π-unital-algebra-Commutative-Ring :
      left-unit-law
        ( mul-Π-unital-algebra-Commutative-Ring)
        ( one-Π-unital-algebra-Commutative-Ring)
    left-unit-law-mul-Π-unital-algebra-Commutative-Ring f =
      eq-htpy
        ( λ i → left-unit-law-mul-unital-algebra-Commutative-Ring R (A i) (f i))

    right-unit-law-mul-Π-unital-algebra-Commutative-Ring :
      right-unit-law
        ( mul-Π-unital-algebra-Commutative-Ring)
        ( one-Π-unital-algebra-Commutative-Ring)
    right-unit-law-mul-Π-unital-algebra-Commutative-Ring f =
      eq-htpy
        ( λ i →
          right-unit-law-mul-unital-algebra-Commutative-Ring R (A i) (f i))

  Π-unital-algebra-Commutative-Ring :
    unital-algebra-Commutative-Ring (l2 ⊔ l3) R
  Π-unital-algebra-Commutative-Ring =
    ( algebra-Π-unital-algebra-Commutative-Ring ,
      one-Π-unital-algebra-Commutative-Ring ,
      left-unit-law-mul-Π-unital-algebra-Commutative-Ring ,
      right-unit-law-mul-Π-unital-algebra-Commutative-Ring)
```
