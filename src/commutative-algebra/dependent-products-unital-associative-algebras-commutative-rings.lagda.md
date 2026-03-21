# Dependent products of unital associative algebras over commutative rings

```agda
module commutative-algebra.dependent-products-unital-associative-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.dependent-products-associative-algebras-commutative-rings
open import commutative-algebra.dependent-products-unital-algebras-commutative-rings
open import commutative-algebra.unital-algebras-commutative-rings
open import commutative-algebra.unital-associative-algebras-commutative-rings

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

The dependent product of a family of
[unital associative algebras](commutative-algebra.unital-associative-algebras-commutative-rings.md)
over a [commutative ring](commutative-algebra.commutative-rings.md) is a unital
associative algebra.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (I : UU l2)
  (A : I → unital-associative-algebra-Commutative-Ring l3 R)
  where

  associative-algebra-Π-unital-associative-algebra-Commutative-Ring :
    associative-algebra-Commutative-Ring (l2 ⊔ l3) R
  associative-algebra-Π-unital-associative-algebra-Commutative-Ring =
    Π-associative-algebra-Commutative-Ring
      ( R)
      ( I)
      ( λ i → associative-algebra-unital-associative-algebra-Commutative-Ring
        ( R)
        ( A i))

  unital-algebra-Π-unital-associative-algebra-Commutative-Ring :
    unital-algebra-Commutative-Ring (l2 ⊔ l3) R
  unital-algebra-Π-unital-associative-algebra-Commutative-Ring =
    Π-unital-algebra-Commutative-Ring
      ( R)
      ( I)
      ( λ i → unital-algebra-unital-associative-algebra-Commutative-Ring
        ( R)
        ( A i))

  Π-unital-associative-algebra-Commutative-Ring :
    unital-associative-algebra-Commutative-Ring (l2 ⊔ l3) R
  Π-unital-associative-algebra-Commutative-Ring =
    ( associative-algebra-Π-unital-associative-algebra-Commutative-Ring ,
      pr2 unital-algebra-Π-unital-associative-algebra-Commutative-Ring)
```
