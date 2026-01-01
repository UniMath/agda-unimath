# Algebras over Heyting fields

```agda
module linear-algebra.algebras-heyting-fields where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import commutative-algebra.heyting-fields
open import foundation.dependent-pair-types
open import foundation.sets
open import group-theory.abelian-groups
open import linear-algebra.algebras-commutative-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

## Definition

```agda
algebra-Heyting-Field :
  {l1 : Level} (l2 : Level) → Heyting-Field l1 → UU (l1 ⊔ lsuc l2)
algebra-Heyting-Field l2 F =
  algebra-Commutative-Ring l2 (commutative-ring-Heyting-Field F)
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (A : algebra-Heyting-Field l2 F)
  where

  vector-space-algebra-Heyting-Field : Vector-Space l2 F
  vector-space-algebra-Heyting-Field = pr1 A

  ab-add-algebra-Heyting-Field : Ab l2
  ab-add-algebra-Heyting-Field =
    ab-Vector-Space F vector-space-algebra-Heyting-Field

  set-algebra-Heyting-Field : Set l2
  set-algebra-Heyting-Field = set-Ab ab-add-algebra-Heyting-Field

  type-algebra-Heyting-Field : UU l2
  type-algebra-Heyting-Field = type-Ab ab-add-algebra-Heyting-Field

  zero-algebra-Heyting-Field : type-algebra-Heyting-Field
  zero-algebra-Heyting-Field = zero-Ab ab-add-algebra-Heyting-Field

  add-algebra-Heyting-Field :
    type-algebra-Heyting-Field → type-algebra-Heyting-Field →
    type-algebra-Heyting-Field
  add-algebra-Heyting-Field = add-Ab ab-add-algebra-Heyting-Field

  neg-algebra-Heyting-Field :
    type-algebra-Heyting-Field → type-algebra-Heyting-Field
  neg-algebra-Heyting-Field = neg-Ab ab-add-algebra-Heyting-Field

  mul-algebra-Heyting-Field :
    type-algebra-Heyting-Field → type-algebra-Heyting-Field →
    type-algebra-Heyting-Field
  mul-algebra-Heyting-Field =
    mul-algebra-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( A)
```
