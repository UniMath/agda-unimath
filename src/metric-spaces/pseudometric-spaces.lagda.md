# Pseudometric spaces

```agda
module metric-spaces.pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.monotonic-rational-neighborhoods
open import metric-spaces.preimage-rational-neighborhoods
open import metric-spaces.rational-neighborhoods
open import metric-spaces.reflexive-rational-neighborhoods
open import metric-spaces.saturated-rational-neighborhoods
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
```

</details>

## Idea

A {{#concept "pseudometric space" Agda=Pseudometric-Space}} is a type equipped
with a {{concept "pseudometric structure" Agda=Pseudometric-Structure}}: a
[reflexive](metric-spaces.reflexive-rational-neighborhoods.md),
[symmetric](metric-spaces.symmetric-rational-neighborhoods.md),
[triangular](metric-spaces.triangular-rational-neighborhoods.md) and
[saturated](metric-spaces.saturated-rational-neighborhoods.md)
[rational neighborhood relation](metric-spaces.rational-neighborhoods.md).

Given a pseudometric structure `B` on `A` and some [positive rational number](elementary-number-theory.positive-rational-numbers.md)
`d : ℚ⁺` such that `B d x y` holds for some pair of points `x y : A`, we
interpret `d` as an
{{#concept "upper bound" Disambiguation="on distance in a pseudometric space" Agda=is-upper-bound-dist-Pseudometric-Space}}
on the distance between `x` and `y` in the pseudometric space.

## Definitions

### The property of being a pseudometric structure

```agda
module _
  {l1 : Level} (A : UU l1) {l2 : Level}
  (B : Rational-Neighborhood-Relation l2 A)
  where

  is-pseudometric-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2)
  is-pseudometric-prop-Rational-Neighborhood-Relation =
    product-Prop
      ( is-reflexive-prop-Rational-Neighborhood-Relation B)
      ( product-Prop
        ( is-symmetric-prop-Rational-Neighborhood-Relation B)
        ( product-Prop
          ( is-triangular-prop-Rational-Neighborhood-Relation B)
          ( is-saturated-prop-Rational-Neighborhood-Relation B)))

  is-pseudometric-Rational-Neighborhood-Relation : UU (l1 ⊔ l2)
  is-pseudometric-Rational-Neighborhood-Relation =
    type-Prop is-pseudometric-prop-Rational-Neighborhood-Relation

  is-prop-is-pseudometric-Rational-Neighborhood-Relation :
    is-prop is-pseudometric-Rational-Neighborhood-Relation
  is-prop-is-pseudometric-Rational-Neighborhood-Relation =
    is-prop-type-Prop (is-pseudometric-prop-Rational-Neighborhood-Relation)

Pseudometric-Structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Pseudometric-Structure l2 A =
  type-subtype (is-pseudometric-prop-Rational-Neighborhood-Relation A {l2})
```

### The type of pseudometric spaces

```agda
Pseudometric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Pseudometric-Space l1 l2 = Σ (UU l1) (Pseudometric-Structure l2)

module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  type-Pseudometric-Space : UU l1
  type-Pseudometric-Space = pr1 A

  structure-Pseudometric-Space :
    Pseudometric-Structure l2 type-Pseudometric-Space
  structure-Pseudometric-Space = pr2 A

  neighborhood-prop-Pseudometric-Space :
    ℚ⁺ → Relation-Prop l2 type-Pseudometric-Space
  neighborhood-prop-Pseudometric-Space =
    pr1 structure-Pseudometric-Space

  neighborhood-Pseudometric-Space :
    ℚ⁺ → Relation l2 type-Pseudometric-Space
  neighborhood-Pseudometric-Space =
    neighborhood-Rational-Neighborhood-Relation
      neighborhood-prop-Pseudometric-Space

  is-prop-neighborhood-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space) →
    is-prop (neighborhood-Pseudometric-Space d x y)
  is-prop-neighborhood-Pseudometric-Space =
    is-prop-neighborhood-Rational-Neighborhood-Relation
      neighborhood-prop-Pseudometric-Space

  is-upper-bound-dist-prop-Pseudometric-Space :
    (x y : type-Pseudometric-Space) → ℚ⁺ → Prop l2
  is-upper-bound-dist-prop-Pseudometric-Space x y d =
    neighborhood-prop-Pseudometric-Space d x y

  is-upper-bound-dist-Pseudometric-Space :
    (x y : type-Pseudometric-Space) → ℚ⁺ → UU l2
  is-upper-bound-dist-Pseudometric-Space x y d =
    neighborhood-Pseudometric-Space d x y

  is-prop-is-upper-bound-dist-Pseudometric-Space :
    (x y : type-Pseudometric-Space) (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Pseudometric-Space x y d)
  is-prop-is-upper-bound-dist-Pseudometric-Space x y d =
    is-prop-neighborhood-Pseudometric-Space d x y

  is-pseudometric-neighborhood-Pseudometric-Space :
    is-pseudometric-Rational-Neighborhood-Relation
      type-Pseudometric-Space
      neighborhood-prop-Pseudometric-Space
  is-pseudometric-neighborhood-Pseudometric-Space =
    pr2 structure-Pseudometric-Space

  refl-neighborhood-Pseudometric-Space :
    (d : ℚ⁺) (x : type-Pseudometric-Space) →
    neighborhood-Pseudometric-Space d x x
  refl-neighborhood-Pseudometric-Space =
    pr1 is-pseudometric-neighborhood-Pseudometric-Space

  symmetric-neighborhood-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space) →
    neighborhood-Pseudometric-Space d x y →
    neighborhood-Pseudometric-Space d y x
  symmetric-neighborhood-Pseudometric-Space =
    pr1 (pr2 is-pseudometric-neighborhood-Pseudometric-Space)

  inv-neighborhood-Pseudometric-Space :
    {d : ℚ⁺} {x y : type-Pseudometric-Space} →
    neighborhood-Pseudometric-Space d x y →
    neighborhood-Pseudometric-Space d y x
  inv-neighborhood-Pseudometric-Space {d} {x} {y} =
    symmetric-neighborhood-Pseudometric-Space d x y

  triangular-neighborhood-Pseudometric-Space :
    (x y z : type-Pseudometric-Space) (d₁ d₂ : ℚ⁺) →
    neighborhood-Pseudometric-Space d₂ y z →
    neighborhood-Pseudometric-Space d₁ x y →
    neighborhood-Pseudometric-Space (d₁ +ℚ⁺ d₂) x z
  triangular-neighborhood-Pseudometric-Space =
    pr1 (pr2 (pr2 is-pseudometric-neighborhood-Pseudometric-Space))

  saturated-neighborhood-Pseudometric-Space :
    (ε : ℚ⁺) (x y : type-Pseudometric-Space) →
    ((δ : ℚ⁺) → neighborhood-Pseudometric-Space (ε +ℚ⁺ δ) x y) →
    neighborhood-Pseudometric-Space ε x y
  saturated-neighborhood-Pseudometric-Space =
    pr2 (pr2 (pr2 is-pseudometric-neighborhood-Pseudometric-Space))

  monotonic-neighborhood-Pseudometric-Space :
    (x y : type-Pseudometric-Space) (d₁ d₂ : ℚ⁺) →
    le-ℚ⁺ d₁ d₂ →
    neighborhood-Pseudometric-Space d₁ x y →
    neighborhood-Pseudometric-Space d₂ x y
  monotonic-neighborhood-Pseudometric-Space =
    is-monotonic-is-reflexive-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-Pseudometric-Space
      refl-neighborhood-Pseudometric-Space
      triangular-neighborhood-Pseudometric-Space

  iff-le-neighborhood-Pseudometric-Space :
    ( ε : ℚ⁺) (x y : type-Pseudometric-Space) →
    ( neighborhood-Pseudometric-Space ε x y) ↔
    ( (δ : ℚ⁺) → le-ℚ⁺ ε δ → neighborhood-Pseudometric-Space δ x y)
  iff-le-neighborhood-Pseudometric-Space =
    iff-le-neighborhood-saturated-monotonic-Rational-Neighborhood-Relation
      neighborhood-prop-Pseudometric-Space
      monotonic-neighborhood-Pseudometric-Space
      saturated-neighborhood-Pseudometric-Space
```

## Properties

### Characterization of the transport of pseudometric structures along equalities

```agda
equiv-Eq-tr-Pseudometric-Structure :
  {l1 l2 : Level} (A B : UU l1) →
  (P : Pseudometric-Structure l2 A) →
  (Q : Pseudometric-Structure l2 B) →
  (e : A ＝ B) →
  (tr (Pseudometric-Structure l2) e P ＝ Q) ≃
  (Eq-Rational-Neighborhood-Relation
    ( pr1 P)
    ( preimage-Rational-Neighborhood-Relation (map-eq e) (pr1 Q)))
equiv-Eq-tr-Pseudometric-Structure A .A P Q refl =
  ( equiv-Eq-eq-Rational-Neighborhood-Relation (pr1 P) (pr1 Q)) ∘e
  ( extensionality-type-subtype'
    ( is-pseudometric-prop-Rational-Neighborhood-Relation A)
    ( P)
    ( Q))
```

## External links

- [Pseudometric spaces](https://en.wikipedia.org/wiki/Pseudometric_space) at
  Wikipedia
