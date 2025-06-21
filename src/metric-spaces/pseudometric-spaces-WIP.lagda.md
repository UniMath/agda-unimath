# Pseudometric spaces (WIP)

```agda
module metric-spaces.pseudometric-spaces-WIP where
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
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.monotonic-rational-neighborhoods
open import metric-spaces.rational-neighborhoods
open import metric-spaces.reflexive-rational-neighborhoods
open import metric-spaces.saturated-rational-neighborhoods
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
```

</details>

## Idea

A {{#concept "pseudometric space" Agda=Pseudometric-Space-WIP}} is a type
equipped with a
{{concept "pseudometric structure" Agda=Pseudometric-Structure}}: a
[reflexive](metric-spaces.reflexive-rational-neighborhoods.md),
[symmetric](metric-spaces.symmetric-rational-neighborhoods.md),
[triangular](metric-spaces.triangular-rational-neighborhoods.md) and
[saturated](metric-spaces.saturated-rational-neighborhoods.md)
[rational neighborhood relation](metric-spaces.rational-neighborhoods.md)

Given a pseudometric structure `B` on `A` and some positive rational number
`d : ℚ⁺` such that `B d x y` holds for some pair of points `x y : A`, we
interpret `d` as an
{{#concept "upper bound" Disambiguation="on distance in a pseudometric space" Agda=is-upper-bound-dist-Pseudometric-Space-WIP}}
on the distance between `x` and `y` in the pseudometric space.

## Definitions

### The property of being a premetric structure

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

### Pseudometric spaces

```agda
Pseudometric-Space-WIP : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Pseudometric-Space-WIP l1 l2 = Σ (UU l1) (Pseudometric-Structure l2)

module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  type-Pseudometric-Space-WIP : UU l1
  type-Pseudometric-Space-WIP = pr1 A

  structure-Pseudometric-Space-WIP :
    Pseudometric-Structure l2 type-Pseudometric-Space-WIP
  structure-Pseudometric-Space-WIP = pr2 A

  neighborhood-prop-Pseudometric-Space-WIP :
    ℚ⁺ → Relation-Prop l2 type-Pseudometric-Space-WIP
  neighborhood-prop-Pseudometric-Space-WIP =
    pr1 structure-Pseudometric-Space-WIP

  neighborhood-Pseudometric-Space-WIP :
    ℚ⁺ → Relation l2 type-Pseudometric-Space-WIP
  neighborhood-Pseudometric-Space-WIP =
    neighborhood-Rational-Neighborhood-Relation
      neighborhood-prop-Pseudometric-Space-WIP

  is-prop-neighborhood-Pseudometric-Space-WIP :
    (d : ℚ⁺) (x y : type-Pseudometric-Space-WIP) →
    is-prop (neighborhood-Pseudometric-Space-WIP d x y)
  is-prop-neighborhood-Pseudometric-Space-WIP =
    is-prop-neighborhood-Rational-Neighborhood-Relation
      neighborhood-prop-Pseudometric-Space-WIP

  is-upper-bound-dist-prop-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP) → ℚ⁺ → Prop l2
  is-upper-bound-dist-prop-Pseudometric-Space-WIP x y d =
    neighborhood-prop-Pseudometric-Space-WIP d x y

  is-upper-bound-dist-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP) → ℚ⁺ → UU l2
  is-upper-bound-dist-Pseudometric-Space-WIP x y d =
    neighborhood-Pseudometric-Space-WIP d x y

  is-prop-is-upper-bound-dist-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP) (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Pseudometric-Space-WIP x y d)
  is-prop-is-upper-bound-dist-Pseudometric-Space-WIP x y d =
    is-prop-neighborhood-Pseudometric-Space-WIP d x y

  is-pseudometric-neighborhood-Pseudometric-Space-WIP :
    is-pseudometric-Rational-Neighborhood-Relation
      type-Pseudometric-Space-WIP
      neighborhood-prop-Pseudometric-Space-WIP
  is-pseudometric-neighborhood-Pseudometric-Space-WIP =
    pr2 structure-Pseudometric-Space-WIP

  refl-neighborhood-Pseudometric-Space-WIP :
    (d : ℚ⁺) (x : type-Pseudometric-Space-WIP) →
    neighborhood-Pseudometric-Space-WIP d x x
  refl-neighborhood-Pseudometric-Space-WIP =
    pr1 is-pseudometric-neighborhood-Pseudometric-Space-WIP

  symmetric-neighborhood-Pseudometric-Space-WIP :
    (d : ℚ⁺) (x y : type-Pseudometric-Space-WIP) →
    neighborhood-Pseudometric-Space-WIP d x y →
    neighborhood-Pseudometric-Space-WIP d y x
  symmetric-neighborhood-Pseudometric-Space-WIP =
    pr1 (pr2 is-pseudometric-neighborhood-Pseudometric-Space-WIP)

  inv-neighborhood-Pseudometric-Space-WIP :
    {d : ℚ⁺} {x y : type-Pseudometric-Space-WIP} →
    neighborhood-Pseudometric-Space-WIP d x y →
    neighborhood-Pseudometric-Space-WIP d y x
  inv-neighborhood-Pseudometric-Space-WIP {d} {x} {y} =
    symmetric-neighborhood-Pseudometric-Space-WIP d x y

  triangular-neighborhood-Pseudometric-Space-WIP :
    (x y z : type-Pseudometric-Space-WIP) (d₁ d₂ : ℚ⁺) →
    neighborhood-Pseudometric-Space-WIP d₂ y z →
    neighborhood-Pseudometric-Space-WIP d₁ x y →
    neighborhood-Pseudometric-Space-WIP (d₁ +ℚ⁺ d₂) x z
  triangular-neighborhood-Pseudometric-Space-WIP =
    pr1 (pr2 (pr2 is-pseudometric-neighborhood-Pseudometric-Space-WIP))

  saturated-neighborhood-Pseudometric-Space-WIP :
    (ε : ℚ⁺) (x y : type-Pseudometric-Space-WIP) →
    ((δ : ℚ⁺) → neighborhood-Pseudometric-Space-WIP (ε +ℚ⁺ δ) x y) →
    neighborhood-Pseudometric-Space-WIP ε x y
  saturated-neighborhood-Pseudometric-Space-WIP =
    pr2 (pr2 (pr2 is-pseudometric-neighborhood-Pseudometric-Space-WIP))

  monotonic-neighborhood-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP) (d₁ d₂ : ℚ⁺) →
    le-ℚ⁺ d₁ d₂ →
    neighborhood-Pseudometric-Space-WIP d₁ x y →
    neighborhood-Pseudometric-Space-WIP d₂ x y
  monotonic-neighborhood-Pseudometric-Space-WIP =
    is-monotonic-is-reflexive-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-Pseudometric-Space-WIP
      refl-neighborhood-Pseudometric-Space-WIP
      triangular-neighborhood-Pseudometric-Space-WIP

  iff-le-neighborhood-Pseudometric-Space-WIP :
    ( ε : ℚ⁺) (x y : type-Pseudometric-Space-WIP) →
    ( neighborhood-Pseudometric-Space-WIP ε x y) ↔
    ( (δ : ℚ⁺) → le-ℚ⁺ ε δ → neighborhood-Pseudometric-Space-WIP δ x y)
  iff-le-neighborhood-Pseudometric-Space-WIP =
    iff-le-neighborhood-saturated-monotonic-Rational-Neighborhood-Relation
      neighborhood-prop-Pseudometric-Space-WIP
      monotonic-neighborhood-Pseudometric-Space-WIP
      saturated-neighborhood-Pseudometric-Space-WIP
```

## External links

- [Pseudometric spaces](https://en.wikipedia.org/wiki/Pseudometric_space) at
  Wikipedia
