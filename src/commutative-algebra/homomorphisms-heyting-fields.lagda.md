# Homomorphisms of Heyting fields

```agda
module commutative-algebra.homomorphisms-heyting-fields where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields
open import commutative-algebra.homomorphisms-commutative-rings

open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="of Heyting fields" Agda=hom-Heyting-Field}}
of [Heyting fields](commutative-algebra.heyting-fields.md) is a
[homomorphism](commutative-algebra.homomorphisms-commutative-rings.md) between
their underlying [commutative rings](commutative-algebra.commutative-rings.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (G : Heyting-Field l2)
  where

  hom-Heyting-Field : UU (l1 ⊔ l2)
  hom-Heyting-Field =
    hom-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( commutative-ring-Heyting-Field G)
```
