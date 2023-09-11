# Equality of dependent pair types

```agda
module foundation.equality-dependent-pair-types where

open import foundation-core.equality-dependent-pair-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

The operation [`eq-pair-Σ`](foundation-core.equality-dependent-pair-types.md)
can be seen as a "vertical composition" operation that combines an
[identification](foundation-core.identity-types.md) and a
[dependent identification](foundation.dependent-identifications.md) over it into
a single identification. This operation preserves, in the appropriate sense, the
groupoidal structure on dependent identifications.

## Properties

### Interchange law of concatenation and `eq-pair-Σ`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  interchange-concat-eq-pair-Σ :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) {x' : B x} {y' : B y} {z' : B z} →
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q y' z') →
    eq-pair-Σ (p ∙ q) (concat-dependent-identification B p q p' q') ＝
    ( eq-pair-Σ p p' ∙ eq-pair-Σ q q')
  interchange-concat-eq-pair-Σ refl q refl q' = refl
```

### Interchange law for concatenation and `pair-eq-Σ`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  interchange-concat-pair-eq-Σ :
    {x y z : Σ A B} (p : x ＝ y) (q : y ＝ z) →
    pair-eq-Σ (p ∙ q) ＝
    ( pr1 (pair-eq-Σ p) ∙ pr1 (pair-eq-Σ q) ,
      concat-dependent-identification B
        ( pr1 (pair-eq-Σ p))
        ( pr1 (pair-eq-Σ q))
        ( pr2 (pair-eq-Σ p))
        ( pr2 (pair-eq-Σ q)))
  interchange-concat-pair-eq-Σ refl q = refl

  pr1-interchange-concat-pair-eq-Σ :
    {x y z : Σ A B} (p : x ＝ y) (q : y ＝ z) →
    pr1 (pair-eq-Σ (p ∙ q)) ＝ (pr1 (pair-eq-Σ p) ∙ pr1 (pair-eq-Σ q))
  pr1-interchange-concat-pair-eq-Σ p q =
    ap pr1 (interchange-concat-pair-eq-Σ p q)
```

### Distributivity of `inv` over `eq-pair-Σ`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  distributive-inv-eq-pair-Σ :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y') →
    inv (eq-pair-Σ p p') ＝
    eq-pair-Σ (inv p) (inv-dependent-identification B p p')
  distributive-inv-eq-pair-Σ refl refl = refl
```

### Computing `pair-eq-Σ` at an identification of the form `ap f p`

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : A → UU l3} (f : X → Σ A B)
  where

  pair-eq-Σ-ap :
    {x y : X} (p : x ＝ y) →
    pair-eq-Σ (ap f p) ＝
    ( ( ap (pr1 ∘ f) p) ,
      ( substitution-law-tr B (pr1 ∘ f) p ∙ apd (pr2 ∘ f) p))
  pair-eq-Σ-ap refl = refl

  pr1-pair-eq-Σ-ap :
    {x y : X} (p : x ＝ y) →
    pr1 (pair-eq-Σ (ap f p)) ＝ ap (pr1 ∘ f) p
  pr1-pair-eq-Σ-ap refl = refl
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {Y : UU l3} (f : Σ A B → Y)
  where

  ap-eq-pair-Σ :
    { x y : A} (p : x ＝ y) {b : B x} {b' : B y} →
    ( q : dependent-identification B p b b') →
    ap f (eq-pair-Σ p q) ＝ (ap f (eq-pair-Σ p refl) ∙ ap (ev-pair f y) q)
  ap-eq-pair-Σ refl refl = refl
```

## See also

- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Equality proofs in the fiber of a map are characterized in
  [`foundation.equality-fibers-of-maps`](foundation.equality-fibers-of-maps.md).
