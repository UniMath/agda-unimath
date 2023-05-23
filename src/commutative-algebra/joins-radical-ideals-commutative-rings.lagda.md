# Joins of radical ideals in commutative rings

```agda
module commutative-algebra.joins-radical-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.joins-ideals-commutative-rings
open import commutative-algebra.poset-of-radical-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.radical-ideals-generated-by-subsets-commutative-rings
open import commutative-algebra.radicals-of-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.universe-levels

open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

The **join** of a family of
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md)
`α ↦ J α` in a [commutative ring](commutative-algebra.commutative-rings.md) is
the least radical ideal containing each `J α`.

## Definitions

### The universal property of the join of a family of radical ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {I : UU l2} (J : I → radical-ideal-Commutative-Ring l3 A)
  where

  is-join-family-of-radical-ideals-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) → UUω
  is-join-family-of-radical-ideals-Commutative-Ring =
    is-least-upper-bound-family-of-elements-Large-Poset
      ( radical-ideal-Commutative-Ring-Large-Poset A)
      ( J)
```

### The join of a family of radical ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  {I : UU l2} (J : I → radical-ideal-Commutative-Ring l3 A)
  where

  generating-subset-join-family-of-radical-ideals-Commutative-Ring :
    subset-Commutative-Ring (l2 ⊔ l3) A
  generating-subset-join-family-of-radical-ideals-Commutative-Ring =
    generating-subset-join-family-of-ideals-Commutative-Ring A
      ( λ α → ideal-radical-ideal-Commutative-Ring A (J α))

  join-family-of-radical-ideals-Commutative-Ring :
    radical-ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  join-family-of-radical-ideals-Commutative-Ring =
    radical-ideal-subset-Commutative-Ring A
      generating-subset-join-family-of-radical-ideals-Commutative-Ring

  forward-implication-is-join-join-family-of-radical-ideals-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    ((i : I) → leq-radical-ideal-Commutative-Ring A (J i) K) →
    leq-radical-ideal-Commutative-Ring A
      ( join-family-of-radical-ideals-Commutative-Ring)
      ( K)
  forward-implication-is-join-join-family-of-radical-ideals-Commutative-Ring
    K H =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ring A
      ( join-family-of-ideals-Commutative-Ring A
        ( λ α → ideal-radical-ideal-Commutative-Ring A (J α)))
      ( K)
      ( forward-implication-is-join-join-family-of-ideals-Commutative-Ring A
        ( λ α → ideal-radical-ideal-Commutative-Ring A (J α))
        ( ideal-radical-ideal-Commutative-Ring A K)
        ( H))

  backward-implication-is-join-join-family-of-radical-ideals-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    leq-radical-ideal-Commutative-Ring A
      ( join-family-of-radical-ideals-Commutative-Ring)
      ( K) →
    (i : I) → leq-radical-ideal-Commutative-Ring A (J i) K
  backward-implication-is-join-join-family-of-radical-ideals-Commutative-Ring
    K H i x p =
    H ( x)
      ( contains-ideal-radical-of-ideal-Commutative-Ring A
        ( join-family-of-ideals-Commutative-Ring A
          ( λ α → ideal-radical-ideal-Commutative-Ring A (J α)))
        ( x)
        ( backward-implication-is-join-join-family-of-ideals-Commutative-Ring A
          ( λ α → ideal-radical-ideal-Commutative-Ring A (J α))
          ( join-family-of-ideals-Commutative-Ring A
            ( λ α → ideal-radical-ideal-Commutative-Ring A (J α)))
          ( λ t → id)
          ( i)
          ( x)
          ( p)))

  is-join-join-family-of-radical-ideals-Commutative-Ring :
    is-join-family-of-radical-ideals-Commutative-Ring A J
      join-family-of-radical-ideals-Commutative-Ring
  pr1 (is-join-join-family-of-radical-ideals-Commutative-Ring K) =
    forward-implication-is-join-join-family-of-radical-ideals-Commutative-Ring K
  pr2 (is-join-join-family-of-radical-ideals-Commutative-Ring K) =
    backward-implication-is-join-join-family-of-radical-ideals-Commutative-Ring
      K
```
