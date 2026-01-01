# Associative algebras over commutative rings

```agda
module linear-algebra.associative-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import linear-algebra.algebras-commutative-rings
open import foundation.propositions
open import foundation.subtypes
open import foundation.sets
open import foundation.dependent-pair-types
open import commutative-algebra.commutative-rings
open import foundation.universe-levels
```

</details>

## Idea

An [algebra](linear-algebra.algebras-commutative-rings.md) over a
[commutative ring](commutative-algebra.commutative-rings.md) is
{{#concept "associative" Disambiguation="algebra over a commutative ring" WDID=Q744960 WD="associative algebra" Agda=associative-algebra-Commutative-Ring}}
if its multiplication operation is associative.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  is-associative-prop-algebra-Commutative-Ring : Prop l2
  is-associative-prop-algebra-Commutative-Ring =
    Π-Prop
      ( type-algebra-Commutative-Ring R A)
      ( λ x →
        Π-Prop
          ( type-algebra-Commutative-Ring R A)
          ( λ y →
            Π-Prop
              ( type-algebra-Commutative-Ring R A)
              ( λ z →
                Id-Prop
                  ( set-algebra-Commutative-Ring R A)
                  ( mul-algebra-Commutative-Ring R A
                    ( mul-algebra-Commutative-Ring R A x y)
                    ( z))
                  ( mul-algebra-Commutative-Ring R A
                    ( x)
                    ( mul-algebra-Commutative-Ring R A y z)))))

  is-associative-algebra-Commutative-Ring : UU l2
  is-associative-algebra-Commutative-Ring =
    type-Prop is-associative-prop-algebra-Commutative-Ring

associative-algebra-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
associative-algebra-Commutative-Ring l2 R =
  type-subtype
    ( is-associative-prop-algebra-Commutative-Ring {l2 = l2} R)
```

## Properties

### Every commutative ring is an associative algebra over itself

```agda
associative-algebra-commutative-ring-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  associative-algebra-Commutative-Ring l R
associative-algebra-commutative-ring-Commutative-Ring R =
  ( algebra-commutative-ring-Commutative-Ring R ,
    associative-mul-Commutative-Ring R)
```

## External links

- [Associative algebra](https://en.wikipedia.org/wiki/Associative_algebra) on
  Wikipedia
