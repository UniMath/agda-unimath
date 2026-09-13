# Multivariable loop spaces

```agda
module synthetic-homotopy-theory.multivariable-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-triangles-of-identifications
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.path-algebra
open import foundation.propositional-truncations
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.subuniverse-of-truncated-types
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.left-invertible-magmas
open import structured-types.magmas
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cavallos-trick
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

Given a type `I` and a [pointed type](structured-types.pointed-types.md)
`a∗ : A`, we can form the {{#concept "`I`-ary loop space" Agda=multivariable-Ω}}
in `A` as the type `Σ (a : A), (I → (a ＝ a∗))`. This type is canonically
pointed at `(a∗ , refl-htpy)`. We recover the
[standard loop space](synthetic-homotopy-theory.loop-spaces.md) `ΩA` as the
`1+1`-ary loops, there is a unique `1`-ary loop, and we recover `A` itself as
the `∅`-loops. The `𝕊¹`-ary loops correspond to
[loops of loops](synthetic-homotopy-theory.double-loop-spaces.md). Observe that
among pointed types `1+1` represents elements, and so we should interpret
`1+1`-ary as _unary_ loops rather than binary ones, which is consistent with the
fact that `1+1`-ary loops yields the standard loops.

For every point `x` of `I` there is a coherent, associative, and invertible
[H-space structure](structured-types.h-spaces.md) on `I`-ary loops, and moreover
any point `x` of `I` gives a
[pointed equivalence](structured-types.pointed-equivalences.md) between `I`-ary
loops of `A` and `(I,x) →∗ ΩA`.

## Table of files directly related to loop spaces

{{#include tables/loop-spaces-concepts.md}}

## Definitions

### The `I`-ary loop space

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A∗ : Pointed-Type l2)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  type-multivariable-Ω : UU (l1 ⊔ l2)
  type-multivariable-Ω = Σ A (λ a → I → a ＝ a∗)

  refl-multivariable-Ω : type-multivariable-Ω
  refl-multivariable-Ω = (a∗ , refl-htpy)

  multivariable-Ω : Pointed-Type (l1 ⊔ l2)
  multivariable-Ω = (type-multivariable-Ω , refl-multivariable-Ω)
```

## Properties

### Characterizing equality in multivariable loop spaces

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A∗ : Pointed-Type l2}
  where

  Eq-multivariable-Ω :
    (x y : type-multivariable-Ω I A∗) → UU (l1 ⊔ l2)
  Eq-multivariable-Ω (a , p) (b , q) =
    Σ ( a ＝ b)
      ( λ r → (i : I) → coherence-triangle-identifications (p i) (q i) r)

  refl-Eq-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) → Eq-multivariable-Ω x x
  refl-Eq-multivariable-Ω p = (refl , refl-htpy)

  Eq-eq-multivariable-Ω :
    (x y : type-multivariable-Ω I A∗) → x ＝ y → Eq-multivariable-Ω x y
  Eq-eq-multivariable-Ω x .x refl = refl-Eq-multivariable-Ω x

  abstract
    is-torsorial-Eq-multivariable-Ω :
      (x : type-multivariable-Ω I A∗) → is-torsorial (Eq-multivariable-Ω x)
    is-torsorial-Eq-multivariable-Ω (a , p) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id a)
        ( a , refl)
        ( is-torsorial-htpy p)

  is-equiv-Eq-eq-multivariable-Ω :
    (x y : type-multivariable-Ω I A∗) →
    is-equiv (Eq-eq-multivariable-Ω x y)
  is-equiv-Eq-eq-multivariable-Ω x =
    fundamental-theorem-id
      ( is-torsorial-Eq-multivariable-Ω x)
      ( Eq-eq-multivariable-Ω x)

  extensionality-multivariable-Ω :
    (x y : type-multivariable-Ω I A∗) → (x ＝ y) ≃ Eq-multivariable-Ω x y
  extensionality-multivariable-Ω x y =
    ( Eq-eq-multivariable-Ω x y , is-equiv-Eq-eq-multivariable-Ω x y)

  eq-Eq-multivariable-Ω :
    (x y : type-multivariable-Ω I A∗) → Eq-multivariable-Ω x y → x ＝ y
  eq-Eq-multivariable-Ω x y =
    map-inv-equiv (extensionality-multivariable-Ω x y)
```

### Characterizing equality of equality in multivariable loop spaces

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A∗ : Pointed-Type l2}
  (x y : type-multivariable-Ω I A∗)
  where

  Eq²-multivariable-Ω :
    (p q : Eq-multivariable-Ω x y) → UU (l1 ⊔ l2)
  Eq²-multivariable-Ω (p , H) (q , K) =
    Σ (p ＝ q) (λ r → (i : I) → H i ∙ ap (_∙ pr2 y i) r ＝ K i)

  refl-Eq²-multivariable-Ω :
    (p : Eq-multivariable-Ω x y) → Eq²-multivariable-Ω p p
  refl-Eq²-multivariable-Ω p = (refl , right-unit-htpy)

  Eq²-eq-multivariable-Ω :
    (p q : Eq-multivariable-Ω x y) → p ＝ q → Eq²-multivariable-Ω p q
  Eq²-eq-multivariable-Ω p .p refl = refl-Eq²-multivariable-Ω p

  abstract
    is-torsorial-Eq²-multivariable-Ω :
      (p : Eq-multivariable-Ω x y) → is-torsorial (Eq²-multivariable-Ω p)
    is-torsorial-Eq²-multivariable-Ω (a , p) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id a)
        ( a , refl)
        ( is-torsorial-htpy (p ∙h refl-htpy))

  is-equiv-Eq²-eq-multivariable-Ω :
    (p q : Eq-multivariable-Ω x y) → is-equiv (Eq²-eq-multivariable-Ω p q)
  is-equiv-Eq²-eq-multivariable-Ω p =
    fundamental-theorem-id
      ( is-torsorial-Eq²-multivariable-Ω p)
      ( Eq²-eq-multivariable-Ω p)

  extensionality²-multivariable-Ω :
    (p q : Eq-multivariable-Ω x y) → (p ＝ q) ≃ Eq²-multivariable-Ω p q
  extensionality²-multivariable-Ω p q =
    ( Eq²-eq-multivariable-Ω p q , is-equiv-Eq²-eq-multivariable-Ω p q)

  eq-Eq²-multivariable-Ω :
    (p q : Eq-multivariable-Ω x y) → Eq²-multivariable-Ω p q → p ＝ q
  eq-Eq²-multivariable-Ω p q =
    map-inv-equiv (extensionality²-multivariable-Ω p q)
```

### The multivariable loops over a pointed type forms a magma

```agda
module _
  {l1 l2 : Level} (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  mul-multivariable-Ω :
    (a b : type-multivariable-Ω I A∗) → type-multivariable-Ω I A∗
  mul-multivariable-Ω (a , p) (b , q) = (a , (λ x → p x ∙ inv (q i∗) ∙ q x))

  multivariable-Ω-Magma : Magma (l1 ⊔ l2)
  multivariable-Ω-Magma = (type-multivariable-Ω I A∗ , mul-multivariable-Ω)
```

### The coherent H-space of `I`-ary loops, for pointed `I`

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  Eq-left-unit-law-mul-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) →
    Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ (refl-multivariable-Ω I A∗) x)
      ( x)
  Eq-left-unit-law-mul-multivariable-Ω (a , p) =
    (inv (p i∗) , refl-htpy)

  left-unit-law-mul-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) →
    mul-multivariable-Ω I∗ A∗ (refl-multivariable-Ω I A∗) x ＝ x
  left-unit-law-mul-multivariable-Ω x =
    eq-Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ (refl-multivariable-Ω I A∗) x)
      ( x)
      ( Eq-left-unit-law-mul-multivariable-Ω x)

  Eq-right-unit-law-mul-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) →
    Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ x (refl-multivariable-Ω I A∗))
      ( x)
  Eq-right-unit-law-mul-multivariable-Ω x =
    ( refl , right-unit-htpy ∙h right-unit-htpy)

  right-unit-law-mul-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) →
    mul-multivariable-Ω I∗ A∗ x (refl-multivariable-Ω I A∗) ＝ x
  right-unit-law-mul-multivariable-Ω x =
    eq-Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ x (refl-multivariable-Ω I A∗))
      ( x)
      ( Eq-right-unit-law-mul-multivariable-Ω x)

  Eq-coherence-unit-laws-mul-multivariable-Ω :
    Eq²-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗
        ( refl-multivariable-Ω I A∗)
        ( refl-multivariable-Ω I A∗))
      ( refl-multivariable-Ω I A∗)
      ( Eq-left-unit-law-mul-multivariable-Ω (refl-multivariable-Ω I A∗))
      ( Eq-right-unit-law-mul-multivariable-Ω (refl-multivariable-Ω I A∗))
  Eq-coherence-unit-laws-mul-multivariable-Ω =
    ( refl , refl-htpy)

  coherence-unit-laws-mul-multivariable-Ω :
    left-unit-law-mul-multivariable-Ω (refl-multivariable-Ω I A∗) ＝
    right-unit-law-mul-multivariable-Ω (refl-multivariable-Ω I A∗)
  coherence-unit-laws-mul-multivariable-Ω = refl

  multivariable-Ω-H-Space : H-Space (l1 ⊔ l2)
  multivariable-Ω-H-Space =
    ( multivariable-Ω I A∗ ,
      mul-multivariable-Ω I∗ A∗ ,
      left-unit-law-mul-multivariable-Ω ,
      right-unit-law-mul-multivariable-Ω ,
      coherence-unit-laws-mul-multivariable-Ω)
```

### Associativity of multiplication

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  Eq-associative-mul-multivariable-Ω :
    (x y z : type-multivariable-Ω I A∗) →
    Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ (mul-multivariable-Ω I∗ A∗ x y) z)
      ( mul-multivariable-Ω I∗ A∗ x (mul-multivariable-Ω I∗ A∗ y z))
  pr1 (Eq-associative-mul-multivariable-Ω (a , p) (b , q) (c , r)) = refl
  pr2 (Eq-associative-mul-multivariable-Ω (a , p) (b , q) (c , r)) x =
    equational-reasoning
      (((p x ∙ inv (q i∗)) ∙ q x) ∙ inv (r i∗)) ∙ r x
      ＝ (p x ∙ inv (q i∗)) ∙ ((q x ∙ inv (r i∗)) ∙ r x)
        by
        assoc²-1 (p x ∙ inv (q i∗)) (q x) (inv (r i∗)) (r x)
      ＝ (p x ∙ inv ((q i∗ ∙ inv (r i∗)) ∙ r i∗)) ∙ ((q x ∙ inv (r i∗)) ∙ r x)
        by
        ap
          ( λ u → (p x ∙ inv u) ∙ (q x ∙ inv (r i∗) ∙ r x))
          ( inv (is-section-inv-concat' (r i∗) (q i∗)))

  associative-mul-multivariable-Ω :
    (x y z : type-multivariable-Ω I A∗) →
    mul-multivariable-Ω I∗ A∗ (mul-multivariable-Ω I∗ A∗ x y) z ＝
    mul-multivariable-Ω I∗ A∗ x (mul-multivariable-Ω I∗ A∗ y z)
  associative-mul-multivariable-Ω x y z =
    eq-Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ (mul-multivariable-Ω I∗ A∗ x y) z)
      ( mul-multivariable-Ω I∗ A∗ x (mul-multivariable-Ω I∗ A∗ y z))
      ( Eq-associative-mul-multivariable-Ω x y z)
```

### The multiplicative inverse

Given `i∗ : I` and `a∗ : A`, then any `I`-ary loop `(a , p)` has a
multiplicative inverse given by `(a∗ , (i ↦ (p i)⁻¹ ∙ p i∗)`.

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  inv-multivariable-Ω : type-multivariable-Ω I A∗ → type-multivariable-Ω I A∗
  inv-multivariable-Ω (a , p) = (a∗ , (λ i → inv (p i) ∙ p i∗))

  Eq-right-inverse-law-mul-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) →
    Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ x (inv-multivariable-Ω x))
      ( refl-multivariable-Ω I A∗)
  pr1 (Eq-right-inverse-law-mul-multivariable-Ω (a , p)) = p i∗
  pr2 (Eq-right-inverse-law-mul-multivariable-Ω (a , p)) x =
    equational-reasoning
      (p x ∙ inv (inv (p i∗) ∙ p i∗)) ∙ (inv (p x) ∙ p i∗)
      ＝ p x ∙ (inv (p x) ∙ p i∗)
        by
        ap
          ( _∙ (inv (p x) ∙ p i∗))
          ( ap (p x ∙_) (ap inv (left-inv (p i∗))) ∙ right-unit)
      ＝ p i∗
        by is-section-inv-concat (p x) (p i∗)
      ＝ p i∗ ∙ refl
        by inv right-unit

  right-inverse-law-mul-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) →
    mul-multivariable-Ω I∗ A∗ x (inv-multivariable-Ω x) ＝
    refl-multivariable-Ω I A∗
  right-inverse-law-mul-multivariable-Ω x =
    eq-Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ x (inv-multivariable-Ω x))
      ( refl-multivariable-Ω I A∗)
      ( Eq-right-inverse-law-mul-multivariable-Ω x)

  Eq-left-inverse-law-mul-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) →
    Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ (inv-multivariable-Ω x) x)
      ( refl-multivariable-Ω I A∗)
  pr1 (Eq-left-inverse-law-mul-multivariable-Ω (a , p)) = refl
  pr2 (Eq-left-inverse-law-mul-multivariable-Ω (a , p)) i =
    equational-reasoning
      ((inv (p i) ∙ p i∗) ∙ inv (p i∗)) ∙ p i
      ＝ inv (p i) ∙ p i
        by ap (_∙ p i) (is-retraction-inv-concat' (p i∗) (inv (p i)))
      ＝ refl by left-inv (p i)

  left-inverse-law-mul-multivariable-Ω :
    (x : type-multivariable-Ω I A∗) →
    mul-multivariable-Ω I∗ A∗ (inv-multivariable-Ω x) x ＝
    refl-multivariable-Ω I A∗
  left-inverse-law-mul-multivariable-Ω x =
    eq-Eq-multivariable-Ω
      ( mul-multivariable-Ω I∗ A∗ (inv-multivariable-Ω x) x)
      ( refl-multivariable-Ω I A∗)
      ( Eq-left-inverse-law-mul-multivariable-Ω x)
```

### Invertibility of left and right multiplication

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗)
  where

  left-mul-inv-multivariable-Ω :
    (a b : type-multivariable-Ω I A∗) → type-multivariable-Ω I A∗
  left-mul-inv-multivariable-Ω a =
    mul-multivariable-Ω I∗ A∗ (inv-multivariable-Ω I∗ A∗ a)

  is-section-left-mul-inv-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    is-section (mul-multivariable-Ω I∗ A∗ a) (left-mul-inv-multivariable-Ω a)
  is-section-left-mul-inv-multivariable-Ω a x =
    equational-reasoning
      mul-multivariable-Ω I∗ A∗ a
        ( mul-multivariable-Ω I∗ A∗ (inv-multivariable-Ω I∗ A∗ a) x)
      ＝ mul-multivariable-Ω I∗ A∗
          ( mul-multivariable-Ω I∗ A∗ a (inv-multivariable-Ω I∗ A∗ a))
          ( x)
        by
        inv
          ( associative-mul-multivariable-Ω I∗ A∗ a
            ( inv-multivariable-Ω I∗ A∗ a)
            ( x))
      ＝ mul-multivariable-Ω I∗ A∗ (refl-multivariable-Ω I A∗) x
        by
        ap
          ( λ u → mul-multivariable-Ω I∗ A∗ u x)
          ( right-inverse-law-mul-multivariable-Ω I∗ A∗ a)
      ＝ x
        by left-unit-law-mul-multivariable-Ω I∗ A∗ x

  is-retraction-left-mul-inv-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    is-retraction (mul-multivariable-Ω I∗ A∗ a) (left-mul-inv-multivariable-Ω a)
  is-retraction-left-mul-inv-multivariable-Ω a x =
    equational-reasoning
      mul-multivariable-Ω I∗ A∗
        ( inv-multivariable-Ω I∗ A∗ a)
        ( mul-multivariable-Ω I∗ A∗ a x)
      ＝ mul-multivariable-Ω I∗ A∗
          ( mul-multivariable-Ω I∗ A∗ (inv-multivariable-Ω I∗ A∗ a) a)
          ( x)
        by
        inv
          ( associative-mul-multivariable-Ω I∗ A∗
            ( inv-multivariable-Ω I∗ A∗ a)
            ( a)
            ( x))
      ＝ mul-multivariable-Ω I∗ A∗ (refl-multivariable-Ω I A∗) x
        by
        ap
          ( λ u → mul-multivariable-Ω I∗ A∗ u x)
          ( left-inverse-law-mul-multivariable-Ω I∗ A∗ a)
      ＝ x by left-unit-law-mul-multivariable-Ω I∗ A∗ x

  section-left-mul-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) → section (mul-multivariable-Ω I∗ A∗ a)
  section-left-mul-multivariable-Ω a =
    ( left-mul-inv-multivariable-Ω a ,
      is-section-left-mul-inv-multivariable-Ω a)

  retraction-left-mul-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) → retraction (mul-multivariable-Ω I∗ A∗ a)
  retraction-left-mul-multivariable-Ω a =
    ( left-mul-inv-multivariable-Ω a ,
      is-retraction-left-mul-inv-multivariable-Ω a)

  is-equiv-left-mul-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) → is-equiv (mul-multivariable-Ω I∗ A∗ a)
  is-equiv-left-mul-multivariable-Ω a =
    is-equiv-is-invertible
      ( left-mul-inv-multivariable-Ω a)
      ( is-section-left-mul-inv-multivariable-Ω a)
      ( is-retraction-left-mul-inv-multivariable-Ω a)

  equiv-left-mul-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    type-multivariable-Ω I A∗ ≃ type-multivariable-Ω I A∗
  equiv-left-mul-multivariable-Ω a =
    ( mul-multivariable-Ω I∗ A∗ a , is-equiv-left-mul-multivariable-Ω a)

  is-left-invertible-mul-multivariable-Ω :
    is-left-invertible-Magma (multivariable-Ω-Magma I∗ A∗)
  is-left-invertible-mul-multivariable-Ω = is-equiv-left-mul-multivariable-Ω
```

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗)
  where

  right-mul-inv-multivariable-Ω :
    (a b : type-multivariable-Ω I A∗) → type-multivariable-Ω I A∗
  right-mul-inv-multivariable-Ω a x =
    mul-multivariable-Ω I∗ A∗ x (inv-multivariable-Ω I∗ A∗ a)

  is-section-right-mul-inv-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    is-section
      ( λ x → mul-multivariable-Ω I∗ A∗ x a)
      ( right-mul-inv-multivariable-Ω a)
  is-section-right-mul-inv-multivariable-Ω a x =
    equational-reasoning
      mul-multivariable-Ω I∗ A∗
        ( mul-multivariable-Ω I∗ A∗ x (inv-multivariable-Ω I∗ A∗ a))
        ( a)
      ＝ mul-multivariable-Ω I∗ A∗ x
          ( mul-multivariable-Ω I∗ A∗ (inv-multivariable-Ω I∗ A∗ a) a)
        by
        associative-mul-multivariable-Ω I∗ A∗ x (inv-multivariable-Ω I∗ A∗ a) a
      ＝ mul-multivariable-Ω I∗ A∗ x (refl-multivariable-Ω I A∗)
        by
        ap
          ( mul-multivariable-Ω I∗ A∗ x)
          ( left-inverse-law-mul-multivariable-Ω I∗ A∗ a)
      ＝ x
        by right-unit-law-mul-multivariable-Ω I∗ A∗ x

  is-retraction-right-mul-inv-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    is-retraction
      ( λ x → mul-multivariable-Ω I∗ A∗ x a)
      ( right-mul-inv-multivariable-Ω a)
  is-retraction-right-mul-inv-multivariable-Ω a x =
    equational-reasoning
      mul-multivariable-Ω I∗ A∗
        ( mul-multivariable-Ω I∗ A∗ x a)
        ( inv-multivariable-Ω I∗ A∗ a)
      ＝ mul-multivariable-Ω I∗ A∗ x
          ( mul-multivariable-Ω I∗ A∗ a (inv-multivariable-Ω I∗ A∗ a))
        by
        associative-mul-multivariable-Ω I∗ A∗ x a (inv-multivariable-Ω I∗ A∗ a)
      ＝ mul-multivariable-Ω I∗ A∗ x (refl-multivariable-Ω I A∗)
        by
        ap
          ( mul-multivariable-Ω I∗ A∗ x)
          ( right-inverse-law-mul-multivariable-Ω I∗ A∗ a)
      ＝ x
        by right-unit-law-mul-multivariable-Ω I∗ A∗ x

  section-right-mul-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    section (λ x → mul-multivariable-Ω I∗ A∗ x a)
  section-right-mul-multivariable-Ω a =
    ( right-mul-inv-multivariable-Ω a ,
      is-section-right-mul-inv-multivariable-Ω a)

  retraction-right-mul-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    retraction (λ x → mul-multivariable-Ω I∗ A∗ x a)
  retraction-right-mul-multivariable-Ω a =
    ( right-mul-inv-multivariable-Ω a ,
      is-retraction-right-mul-inv-multivariable-Ω a)

  is-equiv-right-mul-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    is-equiv (λ x → mul-multivariable-Ω I∗ A∗ x a)
  is-equiv-right-mul-multivariable-Ω a =
    is-equiv-is-invertible
      ( right-mul-inv-multivariable-Ω a)
      ( is-section-right-mul-inv-multivariable-Ω a)
      ( is-retraction-right-mul-inv-multivariable-Ω a)

  equiv-right-mul-multivariable-Ω :
    (a : type-multivariable-Ω I A∗) →
    type-multivariable-Ω I A∗ ≃ type-multivariable-Ω I A∗
  equiv-right-mul-multivariable-Ω a =
    ( ( λ x → mul-multivariable-Ω I∗ A∗ x a) ,
      ( is-equiv-right-mul-multivariable-Ω a))
```

### If `I` is pointed then `I`-ary loops are pointed equivalent to pointed maps `I →∗ ΩA`

First we demonstrate the equivalence directly as a composite of simple
equivalences, then we construct the explicit map and demonstrate that it is also
pointed.

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  abstract
    compute-type-multivariable-Ω-pointed' :
      type-multivariable-Ω I A∗ ≃ (I∗ →∗ Ω A∗)
    compute-type-multivariable-Ω-pointed' =
      equivalence-reasoning
        Σ A (λ a → I → a ＝ a∗)
        ≃ Σ A (λ a → Σ (I → a ＝ a∗) (λ f → Σ (a ＝ a∗) (f i∗ ＝_)))
          by
          equiv-tot
            ( λ a →
              inv-right-unit-law-Σ-is-contr (λ f → is-torsorial-Id (f i∗)))
        ≃ Σ (Σ A (_＝ a∗)) (λ (a , p) → Σ (I → a ＝ a∗) (λ a → a i∗ ＝ p))
          by inv-associative-Σ ∘e equiv-tot (λ a → equiv-left-swap-Σ)
        ≃ Σ (I → a∗ ＝ a∗) (λ f → f i∗ ＝ refl)
          by left-unit-law-Σ-is-contr (is-torsorial-Id' a∗) (a∗ , refl)

  map-compute-multivariable-Ω-pointed :
    type-multivariable-Ω I A∗ → (I∗ →∗ Ω A∗)
  map-compute-multivariable-Ω-pointed (a , p) =
    ( (λ i → inv (p i∗) ∙ p i) , left-inv (p i∗))

  map-inv-compute-multivariable-Ω-pointed :
    (I∗ →∗ Ω A∗) → type-multivariable-Ω I A∗
  map-inv-compute-multivariable-Ω-pointed (f , p) = (a∗ , f)

  is-section-map-inv-compute-multivariable-Ω-pointed :
    is-section
      map-compute-multivariable-Ω-pointed
      map-inv-compute-multivariable-Ω-pointed
  is-section-map-inv-compute-multivariable-Ω-pointed (f , p) =
    eq-pointed-htpy _ _
      ( cavallos-trick-H-Space' I∗ (Ω-H-Space A∗) _ _
        ( λ x → ap (λ u → inv u ∙ f x) p))

  is-retraction-map-inv-compute-multivariable-Ω-pointed :
    is-retraction
      ( map-compute-multivariable-Ω-pointed)
      ( map-inv-compute-multivariable-Ω-pointed)
  is-retraction-map-inv-compute-multivariable-Ω-pointed (a , p) =
    eq-Eq-multivariable-Ω _ _ (inv (p i∗) , refl-htpy)

  preserves-point-map-compute-multivariable-Ω-pointed :
    map-compute-multivariable-Ω-pointed (refl-multivariable-Ω I A∗) ＝
    ( const I (refl-Ω A∗) , refl)
  preserves-point-map-compute-multivariable-Ω-pointed = refl

  is-equiv-map-compute-multivariable-Ω-pointed :
    is-equiv map-compute-multivariable-Ω-pointed
  is-equiv-map-compute-multivariable-Ω-pointed =
    is-equiv-is-invertible
      ( map-inv-compute-multivariable-Ω-pointed)
      ( is-section-map-inv-compute-multivariable-Ω-pointed)
      ( is-retraction-map-inv-compute-multivariable-Ω-pointed)

  compute-type-multivariable-Ω-pointed :
    type-multivariable-Ω I A∗ ≃ (I∗ →∗ Ω A∗)
  compute-type-multivariable-Ω-pointed =
    ( map-compute-multivariable-Ω-pointed ,
      is-equiv-map-compute-multivariable-Ω-pointed)

  compute-multivariable-Ω-pointed :
    multivariable-Ω I A∗ ≃∗ (I∗ →∗ Ω A∗ , (const I (refl-Ω A∗) , refl))
  compute-multivariable-Ω-pointed =
    ( compute-type-multivariable-Ω-pointed ,
      preserves-point-map-compute-multivariable-Ω-pointed)
```

### ∅-ary loops

```agda
module _
  {l : Level} (A∗ : Pointed-Type l)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  compute-type-multivariable-Ω-empty :
    type-multivariable-Ω empty A∗ ≃ A
  compute-type-multivariable-Ω-empty =
    right-unit-law-Σ-is-contr (λ a → universal-property-empty' (a ＝ a∗))

  map-compute-type-multivariable-Ω-empty :
    type-multivariable-Ω empty A∗ → A
  map-compute-type-multivariable-Ω-empty =
    map-equiv compute-type-multivariable-Ω-empty

  preserves-point-map-compute-multivariable-Ω-empty :
    map-compute-type-multivariable-Ω-empty (refl-multivariable-Ω empty A∗) ＝ a∗
  preserves-point-map-compute-multivariable-Ω-empty = refl

  compute-multivariable-Ω-empty :
    multivariable-Ω empty A∗ ≃∗ A∗
  pr1 compute-multivariable-Ω-empty =
    compute-type-multivariable-Ω-empty
  pr2 compute-multivariable-Ω-empty =
    preserves-point-map-compute-multivariable-Ω-empty
```

### `I+1`-ary loops

`(I + 1)`-ary loops are equivalent to families of loops `I → ΩA`, where `Ω` is
the standard loop type.

```agda
module _
  {l1 l2 : Level} {I : UU l1} (A∗ : Pointed-Type l2)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  compute-type-multivariable-Ω-isolated-point :
    type-multivariable-Ω (I + unit) A∗ ≃ (I → type-Ω A∗)
  compute-type-multivariable-Ω-isolated-point =
    equivalence-reasoning
      Σ A (λ a → I + unit → a ＝ a∗)
      ≃ Σ A (λ a → (I → a ＝ a∗) × (a ＝ a∗))
        by equiv-tot (λ a → equiv-universal-property-Maybe)
      ≃ Σ A (λ a → (a ＝ a∗) × (I → a ＝ a∗))
        by equiv-tot (λ a → commutative-product)
      ≃ Σ (Σ A (λ a → (a ＝ a∗))) (λ u → (I → pr1 u ＝ a∗))
        by inv-associative-Σ
      ≃ (I → type-Ω A∗)
        by left-unit-law-Σ-is-contr (is-torsorial-Id' a∗) (a∗ , refl)
```

### `ΣI`-ary loops are `I`-ary loops of loops

For every type $I$ we have an equivalence

$$Ω_{ΣI}(A) ≃ Ω_I(Ω(A))$$

where $ΣI$ denotes the
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) of $I$.

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A∗ : Pointed-Type l2)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  compute-type-multivariable-Ω-suspension :
    type-multivariable-Ω (suspension I) A∗ ≃ type-multivariable-Ω I (Ω A∗)
  compute-type-multivariable-Ω-suspension =
    equivalence-reasoning
      Σ A (λ a → suspension I → a ＝ a∗)
      ≃ Σ A (λ a → Σ (a ＝ a∗) (λ S → Σ (a ＝ a∗) (λ N → I → N ＝ S)))
        by equiv-tot (λ a → equiv-left-swap-Σ ∘e equiv-up-suspension)
      ≃ Σ (Σ A (λ a → a ＝ a∗)) (λ (a , S) → Σ (a ＝ a∗) (λ N → I → N ＝ S))
        by inv-associative-Σ
      ≃ Σ (a∗ ＝ a∗) (λ N → I → N ＝ refl)
        by left-unit-law-Σ-is-contr (is-torsorial-Id' a∗) (a∗ , refl-Ω A∗)
```

### Truncatedness of `I`-ary loops

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A∗ : Pointed-Type l2)
  where abstract

  is-trunc-type-multivariable-Ω-has-element :
    (k : 𝕋) → I → is-trunc (succ-𝕋 k) (type-Pointed-Type A∗) →
    is-trunc k (type-multivariable-Ω I A∗)
  is-trunc-type-multivariable-Ω-has-element k i∗ K =
    is-trunc-equiv k ((I , i∗) →∗ Ω A∗)
      ( compute-type-multivariable-Ω-pointed (I , i∗) A∗)
      ( is-trunc-pointed-function-type k
        ( K (point-Pointed-Type A∗) (point-Pointed-Type A∗)))

  is-trunc-type-multivariable-Ω-is-inhabited :
    (k : 𝕋) → is-inhabited I → is-trunc (succ-𝕋 k) (type-Pointed-Type A∗) →
    is-trunc k (type-multivariable-Ω I A∗)
  is-trunc-type-multivariable-Ω-is-inhabited k H K =
    rec-trunc-Prop
      ( is-trunc-Prop k (type-multivariable-Ω I A∗))
      ( λ i∗ → is-trunc-type-multivariable-Ω-has-element k i∗ K)
      ( H)
```
