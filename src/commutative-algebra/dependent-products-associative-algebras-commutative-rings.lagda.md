# Dependent products of associative algebras

```agda
module commutative-algebra.dependent-products-associative-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.dependent-products-algebras-commutative-rings

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels
```

</details>

## Idea

Given a [commutative ring](commutative-algebra.commutative-rings.md) `R` and a
family of
[associative algebras](commutative-algebra.associative-algebras-commutative-rings.md)
`Aᵢ` over `R` indexed by `i : I`, the dependent product `Π (i : I) Aᵢ` is an
associative algebra over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (I : UU l2)
  (A : I → associative-algebra-Commutative-Ring l3 R)
  where

  algebra-Π-associative-algebra-Commutative-Ring :
    algebra-Commutative-Ring (l2 ⊔ l3) R
  algebra-Π-associative-algebra-Commutative-Ring =
    Π-algebra-Commutative-Ring R
      ( I)
      ( λ i → algebra-associative-algebra-Commutative-Ring R (A i))

  abstract
    is-associative-algebra-Π-associative-algebra-Commutative-Ring :
      is-associative-algebra-Commutative-Ring
        ( R)
        ( algebra-Π-associative-algebra-Commutative-Ring)
    is-associative-algebra-Π-associative-algebra-Commutative-Ring f g h =
      eq-htpy
        ( λ i →
          associative-mul-associative-algebra-Commutative-Ring
            ( R)
            ( A i)
            ( f i)
            ( g i)
            ( h i))

  Π-associative-algebra-Commutative-Ring :
    associative-algebra-Commutative-Ring (l2 ⊔ l3) R
  Π-associative-algebra-Commutative-Ring =
    ( algebra-Π-associative-algebra-Commutative-Ring ,
      is-associative-algebra-Π-associative-algebra-Commutative-Ring)
```
