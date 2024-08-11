# Neighbourhood relations on types

```agda
module metric-spaces.neighbourhood-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A neighbourhood-relation is a type family of proposition-valued binary relations
indexed by the positive rational numbers.

## Definitions

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Neighbourhood-Relation-Prop : UU (l1 ⊔ (lsuc l2))
  Neighbourhood-Relation-Prop = ℚ⁺ → Relation-Prop l2 A
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Neighbourhood-Relation-Prop l2 A)
  where

  is-in-Neighbourhood : ℚ⁺ → A → A → UU l2
  is-in-Neighbourhood d = type-Relation-Prop (B d)

  is-prop-is-in-Neighbourhood :
    (d : ℚ⁺) (x y : A) → is-prop (is-in-Neighbourhood d x y)
  is-prop-is-in-Neighbourhood d = is-prop-type-Relation-Prop (B d)
```

### Two elements `x` and `y` are indistinguishable in the neighbourhood-relation `B` if `B d x y` holds for all positive rational numbers d

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Neighbourhood-Relation-Prop l2 A)
  (x y : A)
  where

  is-indistinguishable-Neighbourhood-Prop : Prop l2
  is-indistinguishable-Neighbourhood-Prop =
    Π-Prop ℚ⁺ (λ (d : ℚ⁺) → B d x y)

  is-indistinguishable-Neighbourhood : UU l2
  is-indistinguishable-Neighbourhood =
    type-Prop is-indistinguishable-Neighbourhood-Prop

  is-prop-is-indistinguishable-Neighbourhood :
    is-prop is-indistinguishable-Neighbourhood
  is-prop-is-indistinguishable-Neighbourhood =
    is-prop-type-Prop is-indistinguishable-Neighbourhood-Prop
```

## Properties

### A neighbourhood-relation `B` is reflexive if `B d` is reflexive for all positive rational numbers `d`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Neighbourhood-Relation-Prop l2 A)
  where

  is-reflexive-Neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-reflexive-Neighbourhood-Prop =
    Π-Prop
      ( ℚ⁺)
      ( λ (d : ℚ⁺) →
        ( is-reflexive-Relation-Prop (B d) ,
          is-prop-is-reflexive-Relation-Prop (B d)))

  is-reflexive-Neighbourhood : UU (l1 ⊔ l2)
  is-reflexive-Neighbourhood = type-Prop is-reflexive-Neighbourhood-Prop

  is-prop-is-reflexive-Neighbourhood : is-prop is-reflexive-Neighbourhood
  is-prop-is-reflexive-Neighbourhood =
    is-prop-type-Prop is-reflexive-Neighbourhood-Prop
```

### A neighbourhood-relation `B` is symmetric if `B d` is symmetric for all positive rational numbers d

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Neighbourhood-Relation-Prop l2 A)
  where

  is-symmetric-Neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-symmetric-Neighbourhood-Prop =
    Π-Prop
      ( ℚ⁺)
      ( λ (d : ℚ⁺) →
        ( is-symmetric-Relation-Prop (B d) ,
          is-prop-is-symmetric-Relation-Prop (B d)))

  is-symmetric-Neighbourhood : UU (l1 ⊔ l2)
  is-symmetric-Neighbourhood = type-Prop is-symmetric-Neighbourhood-Prop

  is-prop-is-symmetric-Neighbourhood : is-prop is-symmetric-Neighbourhood
  is-prop-is-symmetric-Neighbourhood =
    is-prop-type-Prop is-symmetric-Neighbourhood-Prop
```

### A neighbourhood-relation is tight if any two indistinguishable elements are equal

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Neighbourhood-Relation-Prop l2 A)
  where

  is-tight-Neighbourhood : UU (l1 ⊔ l2)
  is-tight-Neighbourhood =
    (x y : A) → is-indistinguishable-Neighbourhood B x y → x ＝ y
```

### A neighbourhood-relation is monotonic if `B d₁ x y` implies `B d₂ x y` for any positive rational numbers `d₁` and `d₂` with `d₁ < d₂`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Neighbourhood-Relation-Prop l2 A)
  where

  is-monotonic-Neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-monotonic-Neighbourhood-Prop =
    Π-Prop
      ( A)
      ( λ x →
        ( Π-Prop
          ( A)
          ( λ y →
            ( Π-Prop
              ( ℚ⁺)
              ( λ d₁ →
                ( Π-Prop
                  ( ℚ⁺)
                  ( λ d₂ →
                    ( Π-Prop
                      ( le-ℚ⁺ d₁ d₂)
                      ( λ H →
                        hom-Prop (B d₁ x y) (B d₂ x y))))))))))

  is-monotonic-Neighbourhood : UU (l1 ⊔ l2)
  is-monotonic-Neighbourhood = type-Prop is-monotonic-Neighbourhood-Prop

  is-prop-is-monotonic-Neighbourhood : is-prop is-monotonic-Neighbourhood
  is-prop-is-monotonic-Neighbourhood =
    is-prop-type-Prop is-monotonic-Neighbourhood-Prop
```

### A neighbourhood-relation is triangular if it is additively transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Neighbourhood-Relation-Prop l2 A)
  where

  is-triangular-Neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-triangular-Neighbourhood-Prop =
    Π-Prop
      ( A)
      ( λ x →
        ( Π-Prop
          ( A)
          ( λ y →
            ( Π-Prop
              ( A)
              ( λ z →
                Π-Prop
                  ( ℚ⁺)
                  ( λ d₁ →
                    ( Π-Prop
                      ( ℚ⁺)
                      ( λ d₂ →
                        hom-Prop
                          ( B d₂ y z)
                          ( hom-Prop
                            ( B d₁ x y)
                            ( B (d₁ +ℚ⁺ d₂) x z))))))))))

  is-triangular-Neighbourhood : UU (l1 ⊔ l2)
  is-triangular-Neighbourhood = type-Prop is-triangular-Neighbourhood-Prop

  is-prop-is-triangular-Neighbourhood : is-prop is-triangular-Neighbourhood
  is-prop-is-triangular-Neighbourhood =
    is-prop-type-Prop is-triangular-Neighbourhood-Prop
```

### Any triangular reflexive neighbourhood-relation is monotonic

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Neighbourhood-Relation-Prop l2 A)
  where

  is-monotonic-is-reflexive-triangular-Neighbourhood :
    is-reflexive-Neighbourhood B →
    is-triangular-Neighbourhood B →
    is-monotonic-Neighbourhood B
  is-monotonic-is-reflexive-triangular-Neighbourhood H K x y d₁ d₂ I B₁ =
    tr
      ( λ d → is-in-Neighbourhood B d x y)
      ( right-diff-law-add-ℚ⁺ d₁ d₂ I)
      ( K x y y d₁ (le-diff-ℚ⁺ d₁ d₂ I)
        ( H (le-diff-ℚ⁺ d₁ d₂ I) y)
        ( B₁))
```

## External links

- [MetricSpaces.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology
