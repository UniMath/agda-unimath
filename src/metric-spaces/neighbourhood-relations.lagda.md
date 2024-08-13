# Neighbourhood relations on types

```agda
module metric-spaces.neighbourhood-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
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

  neighbourhood-Relation-Prop : UU (l1 ⊔ (lsuc l2))
  neighbourhood-Relation-Prop = ℚ⁺ → Relation-Prop l2 A
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  where

  is-in-neighbourhood : ℚ⁺ → A → A → UU l2
  is-in-neighbourhood d = type-Relation-Prop (B d)

  is-prop-is-in-neighbourhood :
    (d : ℚ⁺) (x y : A) → is-prop (is-in-neighbourhood d x y)
  is-prop-is-in-neighbourhood d = is-prop-type-Relation-Prop (B d)
```

### Two elements `x` and `y` are indistinguishable in the neighbourhood-relation `B` if `B d x y` holds for all positive rational numbers d

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  (x y : A)
  where

  is-indistinguishable-in-neighbourhood-Prop : Prop l2
  is-indistinguishable-in-neighbourhood-Prop =
    Π-Prop ℚ⁺ (λ (d : ℚ⁺) → B d x y)

  is-indistinguishable-in-neighbourhood : UU l2
  is-indistinguishable-in-neighbourhood =
    type-Prop is-indistinguishable-in-neighbourhood-Prop

  is-prop-is-indistinguishable-in-neighbourhood :
    is-prop is-indistinguishable-in-neighbourhood
  is-prop-is-indistinguishable-in-neighbourhood =
    is-prop-type-Prop is-indistinguishable-in-neighbourhood-Prop
```

## Properties

### A neighbourhood-relation `B` is reflexive if `B d` is reflexive for all positive rational numbers `d`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  where

  is-reflexive-neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-reflexive-neighbourhood-Prop =
    Π-Prop ℚ⁺ (is-reflexive-prop-Relation-Prop ∘ B)

  is-reflexive-neighbourhood : UU (l1 ⊔ l2)
  is-reflexive-neighbourhood = type-Prop is-reflexive-neighbourhood-Prop

  is-prop-is-reflexive-neighbourhood : is-prop is-reflexive-neighbourhood
  is-prop-is-reflexive-neighbourhood =
    is-prop-type-Prop is-reflexive-neighbourhood-Prop
```

### In a reflexive neighbourhood-relation, equal elements are indistinguishable

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  (H : is-reflexive-neighbourhood B)
  where

  indistinguishable-eq-reflexive-neighbourhood :
    (x y : A) → x ＝ y → is-indistinguishable-in-neighbourhood B x y
  indistinguishable-eq-reflexive-neighbourhood x .x refl d = H d x
```

### A neighbourhood-relation `B` is symmetric if `B d` is symmetric for all positive rational numbers d

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  where

  is-symmetric-neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-symmetric-neighbourhood-Prop =
    Π-Prop ℚ⁺ (is-symmetric-prop-Relation-Prop ∘ B)

  is-symmetric-neighbourhood : UU (l1 ⊔ l2)
  is-symmetric-neighbourhood = type-Prop is-symmetric-neighbourhood-Prop

  is-prop-is-symmetric-neighbourhood : is-prop is-symmetric-neighbourhood
  is-prop-is-symmetric-neighbourhood =
    is-prop-type-Prop is-symmetric-neighbourhood-Prop
```

### A neighbourhood-relation is separating if being indistinguishable with an element is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  where

  is-separating-neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-separating-neighbourhood-Prop =
    Π-Prop
      ( A)
      ( λ (x : A) →
        is-prop-Prop (Σ A (is-indistinguishable-in-neighbourhood B x)))

  is-separating-neighbourhood : UU (l1 ⊔ l2)
  is-separating-neighbourhood =
    type-Prop is-separating-neighbourhood-Prop

  is-prop-is-separating-neighbourhood : is-prop is-separating-neighbourhood
  is-prop-is-separating-neighbourhood =
    is-prop-type-Prop is-separating-neighbourhood-Prop
```

### In a reflexive separating neighbourhood-relation, indistinguishability is torsorial

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  (S : is-separating-neighbourhood B) (R : is-reflexive-neighbourhood B)
  where

  is-torsorial-indistinguisable-separating-reflexive-neighbourhood :
    (x : A) →
    is-torsorial (is-indistinguishable-in-neighbourhood B x)
  is-torsorial-indistinguisable-separating-reflexive-neighbourhood x =
    is-proof-irrelevant-is-prop (S x) (x , λ d → R d x)

  is-equiv-indistinguishable-eq-separating-reflexive-neighbourhood :
    (x y : A) → is-equiv (indistinguishable-eq-reflexive-neighbourhood B R x y)
  is-equiv-indistinguishable-eq-separating-reflexive-neighbourhood x =
    fundamental-theorem-id
      ( is-torsorial-indistinguisable-separating-reflexive-neighbourhood x)
      ( indistinguishable-eq-reflexive-neighbourhood B R x)
```

### Any type equipped with a reflexive separating neighbourhood-relation is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  (S : is-separating-neighbourhood B) (R : is-reflexive-neighbourhood B)
  where

  is-set-has-separating-reflexive-neighbourhood : is-set A
  is-set-has-separating-reflexive-neighbourhood x y =
    is-prop-is-equiv
      ( is-equiv-indistinguishable-eq-separating-reflexive-neighbourhood
        B
        S
        R
        x
        y)
      ( is-prop-is-indistinguishable-in-neighbourhood B x y)
```

### A neighbourhood-relation is tight if any two indistinguishable elements are equal

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  where

  is-tight-neighbourhood : UU (l1 ⊔ l2)
  is-tight-neighbourhood =
    (x y : A) → is-indistinguishable-in-neighbourhood B x y → x ＝ y
```

### Any tight neighbourhood-relation is separating

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  (T : is-tight-neighbourhood B)
  where

  all-eq-indistinguishable-tight-neighbourhood :
    (x : A) →
    (u v : Σ A (is-indistinguishable-in-neighbourhood B x)) →
    u ＝ v
  all-eq-indistinguishable-tight-neighbourhood x (u , I) (v , J) =
    eq-type-subtype
      ( is-indistinguishable-in-neighbourhood-Prop B x)
      ( inv (T x u I) ∙ T x v J)

  is-separating-is-tight-neighbourhood : is-separating-neighbourhood B
  is-separating-is-tight-neighbourhood x =
    is-prop-all-elements-equal (all-eq-indistinguishable-tight-neighbourhood x)
```

### Any reflexive separating neighbourhood-relation is tight

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  (S : is-separating-neighbourhood B) (R : is-reflexive-neighbourhood B)
  where

  is-tight-is-separating-reflexive-neighbourhood :
    is-tight-neighbourhood B
  is-tight-is-separating-reflexive-neighbourhood x =
    ( map-inv-is-equiv) ∘
    ( is-equiv-indistinguishable-eq-separating-reflexive-neighbourhood B S R x)
```

### A neighbourhood-relation is monotonic if `B d₁ x y` implies `B d₂ x y` for any positive rational numbers `d₁` and `d₂` with `d₁ < d₂`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  where

  is-monotonic-neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-monotonic-neighbourhood-Prop =
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

  is-monotonic-neighbourhood : UU (l1 ⊔ l2)
  is-monotonic-neighbourhood = type-Prop is-monotonic-neighbourhood-Prop

  is-prop-is-monotonic-neighbourhood : is-prop is-monotonic-neighbourhood
  is-prop-is-monotonic-neighbourhood =
    is-prop-type-Prop is-monotonic-neighbourhood-Prop
```

### A neighbourhood-relation is triangular if it is additively transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  where

  is-triangular-neighbourhood-Prop : Prop (l1 ⊔ l2)
  is-triangular-neighbourhood-Prop =
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

  is-triangular-neighbourhood : UU (l1 ⊔ l2)
  is-triangular-neighbourhood = type-Prop is-triangular-neighbourhood-Prop

  is-prop-is-triangular-neighbourhood : is-prop is-triangular-neighbourhood
  is-prop-is-triangular-neighbourhood =
    is-prop-type-Prop is-triangular-neighbourhood-Prop
```

### Any triangular reflexive neighbourhood-relation is monotonic

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : neighbourhood-Relation-Prop l2 A)
  where

  is-monotonic-is-reflexive-triangular-neighbourhood :
    is-reflexive-neighbourhood B →
    is-triangular-neighbourhood B →
    is-monotonic-neighbourhood B
  is-monotonic-is-reflexive-triangular-neighbourhood H K x y d₁ d₂ I B₁ =
    tr
      ( λ d → is-in-neighbourhood B d x y)
      ( right-diff-law-add-ℚ⁺ d₁ d₂ I)
      ( K x y y d₁ (le-diff-ℚ⁺ d₁ d₂ I)
        ( H (le-diff-ℚ⁺ d₁ d₂ I) y)
        ( B₁))
```

## External links

- [MetricSpaces.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MetricSpaces.Type.html)
  at TypeTopology
