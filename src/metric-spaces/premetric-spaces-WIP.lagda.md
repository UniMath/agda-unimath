# Premetric spaces (WIP)

```agda
module metric-spaces.premetric-spaces-WIP where
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
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
```

</details>

## Idea

A {{#concept "premetric space" Agda=Premetric-Space-WIP}} is a type equipped
with [reflexive](metric-spaces.reflexive-rational-neighborhoods.md),
[symmetric](metric-spaces.symmetric-rational-neighborhoods.md) and
[triangular](metric-spaces.triangular-rational-neighborhoods.md)
[rational neighborhood relation](metric-spaces.rational-neighborhoods.md)

Given a premetric `B` on `A` and some positive rational number `d : ℚ⁺` such
that `B d x y` holds for some pair of points `x y : A`, we interpret `d` as an
{{#concept "upper bound" Disambiguation="on distance with respect to a premetric structure"}}
on the distance between `x` and `y` with respect to the premetric.

## Definitions

### The property of being a premetric structure

```agda
module _
  {l1 : Level} (A : UU l1) {l2 : Level}
  (B : Rational-Neighborhood-Relation l2 A)
  where

  is-premetric-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2)
  is-premetric-prop-Rational-Neighborhood-Relation =
    product-Prop
      ( is-reflexive-prop-Rational-Neighborhood-Relation B)
      ( product-Prop
        ( is-symmetric-prop-Rational-Neighborhood-Relation B)
        ( is-triangular-prop-Rational-Neighborhood-Relation B))

  is-premetric-Rational-Neighborhood-Relation : UU (l1 ⊔ l2)
  is-premetric-Rational-Neighborhood-Relation =
    type-Prop is-premetric-prop-Rational-Neighborhood-Relation

  is-prop-is-premetric-Rational-Neighborhood-Relation :
    is-prop is-premetric-Rational-Neighborhood-Relation
  is-prop-is-premetric-Rational-Neighborhood-Relation =
    is-prop-type-Prop (is-premetric-prop-Rational-Neighborhood-Relation)

Premetric-Structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Premetric-Structure l2 A =
  type-subtype (is-premetric-prop-Rational-Neighborhood-Relation A {l2})
```

### Premetric spaces

```agda
Premetric-Space-WIP : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Premetric-Space-WIP l1 l2 = Σ (UU l1) (Premetric-Structure l2)

module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  type-Premetric-Space-WIP : UU l1
  type-Premetric-Space-WIP = pr1 A

  structure-Premetric-Space-WIP :
    Premetric-Structure l2 type-Premetric-Space-WIP
  structure-Premetric-Space-WIP = pr2 A

  neighborhood-prop-Premetric-Space-WIP :
    Rational-Neighborhood-Relation l2 type-Premetric-Space-WIP
  neighborhood-prop-Premetric-Space-WIP =
    pr1 structure-Premetric-Space-WIP

  neighborhood-Premetric-Space-WIP :
    ℚ⁺ → Relation l2 type-Premetric-Space-WIP
  neighborhood-Premetric-Space-WIP =
    neighborhood-Rational-Neighborhood-Relation
      neighborhood-prop-Premetric-Space-WIP

  is-prop-neighborhood-Premetric-Space-WIP :
    (d : ℚ⁺) (x y : type-Premetric-Space-WIP) →
    is-prop (neighborhood-Premetric-Space-WIP d x y)
  is-prop-neighborhood-Premetric-Space-WIP =
    is-prop-neighborhood-Rational-Neighborhood-Relation
      neighborhood-prop-Premetric-Space-WIP

  is-upper-bound-dist-prop-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP) → ℚ⁺ → Prop l2
  is-upper-bound-dist-prop-Premetric-Space-WIP x y d =
    neighborhood-prop-Premetric-Space-WIP d x y

  is-upper-bound-dist-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP) → ℚ⁺ → UU l2
  is-upper-bound-dist-Premetric-Space-WIP x y d =
    neighborhood-Premetric-Space-WIP d x y

  is-prop-is-upper-bound-dist-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP) (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Premetric-Space-WIP x y d)
  is-prop-is-upper-bound-dist-Premetric-Space-WIP x y d =
    is-prop-neighborhood-Premetric-Space-WIP d x y

  is-premetric-neighborhood-Premetric-Space-WIP :
    is-premetric-Rational-Neighborhood-Relation
      type-Premetric-Space-WIP
      neighborhood-prop-Premetric-Space-WIP
  is-premetric-neighborhood-Premetric-Space-WIP =
    pr2 structure-Premetric-Space-WIP

  refl-neighborhood-Premetric-Space-WIP :
    (d : ℚ⁺) (x : type-Premetric-Space-WIP) →
    neighborhood-Premetric-Space-WIP d x x
  refl-neighborhood-Premetric-Space-WIP =
    pr1 is-premetric-neighborhood-Premetric-Space-WIP

  symmetric-neighborhood-Premetric-Space-WIP :
    (d : ℚ⁺) (x y : type-Premetric-Space-WIP) →
    neighborhood-Premetric-Space-WIP d x y →
    neighborhood-Premetric-Space-WIP d y x
  symmetric-neighborhood-Premetric-Space-WIP =
    pr1 (pr2 is-premetric-neighborhood-Premetric-Space-WIP)

  inv-neighborhood-Premetric-Space-WIP :
    {d : ℚ⁺} {x y : type-Premetric-Space-WIP} →
    neighborhood-Premetric-Space-WIP d x y →
    neighborhood-Premetric-Space-WIP d y x
  inv-neighborhood-Premetric-Space-WIP {d} {x} {y} =
    symmetric-neighborhood-Premetric-Space-WIP d x y

  triangular-neighborhood-Premetric-Space-WIP :
    (x y z : type-Premetric-Space-WIP) (d₁ d₂ : ℚ⁺) →
    neighborhood-Premetric-Space-WIP d₂ y z →
    neighborhood-Premetric-Space-WIP d₁ x y →
    neighborhood-Premetric-Space-WIP (d₁ +ℚ⁺ d₂) x z
  triangular-neighborhood-Premetric-Space-WIP =
    pr2 (pr2 is-premetric-neighborhood-Premetric-Space-WIP)

  monotonic-neighborhood-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP) (d₁ d₂ : ℚ⁺) →
    le-ℚ⁺ d₁ d₂ →
    neighborhood-Premetric-Space-WIP d₁ x y →
    neighborhood-Premetric-Space-WIP d₂ x y
  monotonic-neighborhood-Premetric-Space-WIP =
    is-monotonic-is-reflexive-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-Premetric-Space-WIP
      refl-neighborhood-Premetric-Space-WIP
      triangular-neighborhood-Premetric-Space-WIP
```
