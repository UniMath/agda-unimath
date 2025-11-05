# Multivariable loop spaces

```agda
module synthetic-homotopy-theory.multivariable-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-triangles-of-identifications
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.left-invertible-magmas
open import structured-types.magmas
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

Given a [pointed type](structured-types.pointed-types.md) `i∗ : I`, and a
pointed type `a∗ : A`, we can form the `I`-ary loop space in `A` as the type
`Σ (a : A), (I → (a ＝ a∗))`. We recover the
[standard loops](synthetic-homotopy-theory.loop-spaces.md) as the binary loops,
`A` as the `∅`-ary loops, and there is a unique unary loop.

The type of `I`-ary loops have an associative coherent H-space structure with
right inverses.

## Table of files directly related to loop spaces

{{#include tables/loop-spaces-concepts.md}}

## Definitions

### The `I`-ary loop space

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A∗ : Pointed-Type l2)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  type-multivar-Ω : UU (l1 ⊔ l2)
  type-multivar-Ω = Σ A (λ a → I → a ＝ a∗)

  refl-multivar-Ω : type-multivar-Ω
  refl-multivar-Ω = (a∗ , refl-htpy)

  multivar-Ω : Pointed-Type (l1 ⊔ l2)
  multivar-Ω = (type-multivar-Ω , refl-multivar-Ω)
```

## Properties

### Characterizing equality

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A∗ : Pointed-Type l2}
  where

  Eq-multivar-Ω : (x y : type-multivar-Ω I A∗) → UU (l1 ⊔ l2)
  Eq-multivar-Ω (a , p) (b , q) =
    Σ ( a ＝ b)
      ( λ r → (i : I) → coherence-triangle-identifications (p i) (q i) r)

  refl-Eq-multivar-Ω : (x : type-multivar-Ω I A∗) → Eq-multivar-Ω x x
  refl-Eq-multivar-Ω p = (refl , refl-htpy)

  Eq-eq-multivar-Ω :
    (x y : type-multivar-Ω I A∗) → x ＝ y → Eq-multivar-Ω x y
  Eq-eq-multivar-Ω x .x refl = refl-Eq-multivar-Ω x

  abstract
    is-torsorial-Eq-multivar-Ω :
      (x : type-multivar-Ω I A∗) → is-torsorial (Eq-multivar-Ω x)
    is-torsorial-Eq-multivar-Ω (a , p) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id a)
        ( a , refl)
        ( is-torsorial-htpy p)

  is-equiv-Eq-eq-multivar-Ω :
    (x y : type-multivar-Ω I A∗) → is-equiv (Eq-eq-multivar-Ω x y)
  is-equiv-Eq-eq-multivar-Ω x =
    fundamental-theorem-id (is-torsorial-Eq-multivar-Ω x) (Eq-eq-multivar-Ω x)

  extensionality-multivar-Ω :
    (x y : type-multivar-Ω I A∗) → (x ＝ y) ≃ Eq-multivar-Ω x y
  extensionality-multivar-Ω x y =
    ( Eq-eq-multivar-Ω x y , is-equiv-Eq-eq-multivar-Ω x y)

  eq-Eq-multivar-Ω :
    (x y : type-multivar-Ω I A∗) → Eq-multivar-Ω x y → x ＝ y
  eq-Eq-multivar-Ω x y =
    map-inv-equiv (extensionality-multivar-Ω x y)
```

### Characterizing equality of equality

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A∗ : Pointed-Type l2}
  (x y : type-multivar-Ω I A∗)
  where

  Eq²-multivar-Ω :
    (p q : Eq-multivar-Ω x y) → UU (l1 ⊔ l2)
  Eq²-multivar-Ω (p , H) (q , K) =
    Σ (p ＝ q) (λ r → (i : I) → H i ∙ ap (_∙ pr2 y i) r ＝ K i)

  refl-Eq²-multivar-Ω :
    (p : Eq-multivar-Ω x y) → Eq²-multivar-Ω p p
  refl-Eq²-multivar-Ω p = (refl , right-unit-htpy)

  Eq²-eq-multivar-Ω :
    (p q : Eq-multivar-Ω x y) → p ＝ q → Eq²-multivar-Ω p q
  Eq²-eq-multivar-Ω p .p refl = refl-Eq²-multivar-Ω p

  abstract
    is-torsorial-Eq²-multivar-Ω :
      (p : Eq-multivar-Ω x y) → is-torsorial (Eq²-multivar-Ω p)
    is-torsorial-Eq²-multivar-Ω (a , p) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id a)
        ( a , refl)
        ( is-torsorial-htpy (p ∙h refl-htpy))

  is-equiv-Eq²-eq-multivar-Ω :
    (p q : Eq-multivar-Ω x y) → is-equiv (Eq²-eq-multivar-Ω p q)
  is-equiv-Eq²-eq-multivar-Ω p =
    fundamental-theorem-id
      ( is-torsorial-Eq²-multivar-Ω p)
      ( Eq²-eq-multivar-Ω p)

  extensionality²-multivar-Ω :
    (p q : Eq-multivar-Ω x y) → (p ＝ q) ≃ Eq²-multivar-Ω p q
  extensionality²-multivar-Ω p q =
    ( Eq²-eq-multivar-Ω p q , is-equiv-Eq²-eq-multivar-Ω p q)

  eq-Eq²-multivar-Ω :
    (p q : Eq-multivar-Ω x y) → Eq²-multivar-Ω p q → p ＝ q
  eq-Eq²-multivar-Ω p q =
    map-inv-equiv (extensionality²-multivar-Ω p q)
```

### The `I`-ary loops over a pointed type forms a magma

```agda
module _
  {l1 l2 : Level} (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  mul-multivar-Ω :
    type-multivar-Ω I A∗ → type-multivar-Ω I A∗ → type-multivar-Ω I A∗
  mul-multivar-Ω (a , p) (b , q) = (a , (λ x → p x ∙ inv (q i∗) ∙ q x))

  multivar-Ω-Magma : Magma (l1 ⊔ l2)
  multivar-Ω-Magma = (type-multivar-Ω I A∗ , mul-multivar-Ω)
```

### The coherent H-space of `I`-ary loops on a pointed type

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  Eq-left-unit-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    Eq-multivar-Ω (mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) x) x
  Eq-left-unit-law-mul-multivar-Ω (a , p) = (inv (p i∗) , refl-htpy)

  left-unit-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) x ＝ x
  left-unit-law-mul-multivar-Ω x =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) x)
      ( x)
      ( Eq-left-unit-law-mul-multivar-Ω x)

  Eq-right-unit-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    Eq-multivar-Ω (mul-multivar-Ω I∗ A∗ x (refl-multivar-Ω I A∗)) x
  Eq-right-unit-law-mul-multivar-Ω x =
    ( refl , right-unit-htpy ∙h right-unit-htpy)

  right-unit-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ x (refl-multivar-Ω I A∗) ＝ x
  right-unit-law-mul-multivar-Ω x =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ x (refl-multivar-Ω I A∗))
      ( x)
      ( Eq-right-unit-law-mul-multivar-Ω x)

  Eq-coherence-unit-laws-mul-multivar-Ω :
    Eq²-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) (refl-multivar-Ω I A∗))
      ( refl-multivar-Ω I A∗)
      ( Eq-left-unit-law-mul-multivar-Ω (refl-multivar-Ω I A∗))
      ( Eq-right-unit-law-mul-multivar-Ω (refl-multivar-Ω I A∗))
  Eq-coherence-unit-laws-mul-multivar-Ω =
    ( refl , refl-htpy)

  coherence-unit-laws-mul-multivar-Ω :
    left-unit-law-mul-multivar-Ω (refl-multivar-Ω I A∗) ＝
    right-unit-law-mul-multivar-Ω (refl-multivar-Ω I A∗)
  coherence-unit-laws-mul-multivar-Ω = refl

  multivar-Ω-H-Space : H-Space (l1 ⊔ l2)
  multivar-Ω-H-Space =
    ( multivar-Ω I A∗ ,
      mul-multivar-Ω I∗ A∗ ,
      left-unit-law-mul-multivar-Ω ,
      right-unit-law-mul-multivar-Ω ,
      coherence-unit-laws-mul-multivar-Ω)
```

### Associativity

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  Eq-associative-mul-multivar-Ω :
    (x y z : type-multivar-Ω I A∗) →
    Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ x y) z)
      ( mul-multivar-Ω I∗ A∗ x (mul-multivar-Ω I∗ A∗ y z))
  Eq-associative-mul-multivar-Ω (a , p) (b , q) (c , r) =
    ( refl ,
      λ x →
      equational-reasoning
      (((p x ∙ inv (q i∗)) ∙ q x) ∙ inv (r i∗)) ∙ r x
      ＝ (p x ∙ inv (q i∗)) ∙ ((q x ∙ inv (r i∗)) ∙ r x)
        by
        assoc²-1 (p x ∙ inv (q i∗)) (q x) (inv (r i∗)) (r x)
      ＝ (p x ∙ inv ((q i∗ ∙ inv (r i∗)) ∙ r i∗)) ∙ ((q x ∙ inv (r i∗)) ∙ r x)
        by
        ap
          ( λ u → (p x ∙ inv u) ∙ (q x ∙ inv (r i∗) ∙ r x))
          ( inv (is-section-inv-concat' (r i∗) (q i∗))))

  associative-mul-multivar-Ω :
    (x y z : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ x y) z ＝
    mul-multivar-Ω I∗ A∗ x (mul-multivar-Ω I∗ A∗ y z)
  associative-mul-multivar-Ω x y z =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ x y) z)
      ( mul-multivar-Ω I∗ A∗ x (mul-multivar-Ω I∗ A∗ y z))
      ( Eq-associative-mul-multivar-Ω x y z)
```

### The inverse

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗) (let i∗ = point-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  inv-multivar-Ω : type-multivar-Ω I A∗ → type-multivar-Ω I A∗
  inv-multivar-Ω (a , p) = (a∗ , (λ i → inv (p i) ∙ p i∗))

  Eq-right-inverse-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω x))
      ( refl-multivar-Ω I A∗)
  Eq-right-inverse-law-mul-multivar-Ω (a , p) =
    ( p i∗ ,
      λ x →
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
          by inv right-unit)

  right-inverse-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω x) ＝
    refl-multivar-Ω I A∗
  right-inverse-law-mul-multivar-Ω x =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω x))
      ( refl-multivar-Ω I A∗)
      ( Eq-right-inverse-law-mul-multivar-Ω x)

  Eq-left-inverse-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (inv-multivar-Ω x) x)
      ( refl-multivar-Ω I A∗)
  Eq-left-inverse-law-mul-multivar-Ω (a , p) =
    ( refl ,
      ( λ i →
        equational-reasoning
        ((inv (p i) ∙ p i∗) ∙ inv (p i∗)) ∙ p i
        ＝ inv (p i) ∙ p i
          by ap (_∙ p i) (is-retraction-inv-concat' (p i∗) (inv (p i)))
        ＝ refl by left-inv (p i)))

  left-inverse-law-mul-multivar-Ω :
    (x : type-multivar-Ω I A∗) →
    mul-multivar-Ω I∗ A∗ (inv-multivar-Ω x) x ＝
    refl-multivar-Ω I A∗
  left-inverse-law-mul-multivar-Ω x =
    eq-Eq-multivar-Ω
      ( mul-multivar-Ω I∗ A∗ (inv-multivar-Ω x) x)
      ( refl-multivar-Ω I A∗)
      ( Eq-left-inverse-law-mul-multivar-Ω x)
```

### Invertibility of left and right multiplication

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗)
  where

  left-mul-inv-multivar-Ω :
    type-multivar-Ω I A∗ → type-multivar-Ω I A∗ → type-multivar-Ω I A∗
  left-mul-inv-multivar-Ω a =
    mul-multivar-Ω I∗ A∗ (inv-multivar-Ω I∗ A∗ a)

  is-section-left-mul-inv-multivar-Ω :
    (a : type-multivar-Ω I A∗) →
    is-section (mul-multivar-Ω I∗ A∗ a) (left-mul-inv-multivar-Ω a)
  is-section-left-mul-inv-multivar-Ω a x =
    equational-reasoning
    mul-multivar-Ω I∗ A∗ a (mul-multivar-Ω I∗ A∗ (inv-multivar-Ω I∗ A∗ a) x)
    ＝ mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ a (inv-multivar-Ω I∗ A∗ a)) x
      by inv (associative-mul-multivar-Ω I∗ A∗ a (inv-multivar-Ω I∗ A∗ a) x)
    ＝ mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) x
      by
      ap
        ( λ u → mul-multivar-Ω I∗ A∗ u x)
        ( right-inverse-law-mul-multivar-Ω I∗ A∗ a)
    ＝ x
      by left-unit-law-mul-multivar-Ω I∗ A∗ x

  is-retraction-left-mul-inv-multivar-Ω :
    (a : type-multivar-Ω I A∗) →
    is-retraction (mul-multivar-Ω I∗ A∗ a) (left-mul-inv-multivar-Ω a)
  is-retraction-left-mul-inv-multivar-Ω a x =
    equational-reasoning
    mul-multivar-Ω I∗ A∗
      ( inv-multivar-Ω I∗ A∗ a)
      ( mul-multivar-Ω I∗ A∗ a x)
    ＝ mul-multivar-Ω I∗ A∗
        ( mul-multivar-Ω I∗ A∗ (inv-multivar-Ω I∗ A∗ a) a)
        ( x)
      by
      inv (associative-mul-multivar-Ω I∗ A∗ (inv-multivar-Ω I∗ A∗ a) a x)
    ＝ mul-multivar-Ω I∗ A∗ (refl-multivar-Ω I A∗) x
      by
      ap
        ( λ u → mul-multivar-Ω I∗ A∗ u x)
        ( left-inverse-law-mul-multivar-Ω I∗ A∗ a)
    ＝ x by left-unit-law-mul-multivar-Ω I∗ A∗ x

  section-left-mul-multivar-Ω :
    (a : type-multivar-Ω I A∗) → section (mul-multivar-Ω I∗ A∗ a)
  section-left-mul-multivar-Ω a =
    ( left-mul-inv-multivar-Ω a ,
      is-section-left-mul-inv-multivar-Ω a)

  retraction-left-mul-multivar-Ω :
    (a : type-multivar-Ω I A∗) → retraction (mul-multivar-Ω I∗ A∗ a)
  retraction-left-mul-multivar-Ω a =
    ( left-mul-inv-multivar-Ω a ,
      is-retraction-left-mul-inv-multivar-Ω a)

  is-equiv-left-mul-multivar-Ω :
    (a : type-multivar-Ω I A∗) → is-equiv (mul-multivar-Ω I∗ A∗ a)
  is-equiv-left-mul-multivar-Ω a =
    is-equiv-is-invertible
      ( left-mul-inv-multivar-Ω a)
      ( is-section-left-mul-inv-multivar-Ω a)
      ( is-retraction-left-mul-inv-multivar-Ω a)

  equiv-left-mul-multivar-Ω :
    (a : type-multivar-Ω I A∗) → type-multivar-Ω I A∗ ≃ type-multivar-Ω I A∗
  equiv-left-mul-multivar-Ω a =
    ( mul-multivar-Ω I∗ A∗ a , is-equiv-left-mul-multivar-Ω a)

  is-left-invertible-mul-multivar-Ω :
    is-left-invertible-Magma (multivar-Ω-Magma I∗ A∗)
  is-left-invertible-mul-multivar-Ω = is-equiv-left-mul-multivar-Ω
```

```agda
module _
  {l1 l2 : Level}
  (I∗ : Pointed-Type l1) (A∗ : Pointed-Type l2)
  (let I = type-Pointed-Type I∗)
  (let A = type-Pointed-Type A∗)
  where

  right-mul-inv-multivar-Ω :
    type-multivar-Ω I A∗ → type-multivar-Ω I A∗ → type-multivar-Ω I A∗
  right-mul-inv-multivar-Ω a x =
    mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω I∗ A∗ a)

  is-section-right-mul-inv-multivar-Ω :
    (a : type-multivar-Ω I A∗) →
    is-section
      ( λ x → mul-multivar-Ω I∗ A∗ x a)
      ( right-mul-inv-multivar-Ω a)
  is-section-right-mul-inv-multivar-Ω a x =
    equational-reasoning
    mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω I∗ A∗ a)) a
    ＝ mul-multivar-Ω I∗ A∗ x (mul-multivar-Ω I∗ A∗ (inv-multivar-Ω I∗ A∗ a) a)
      by associative-mul-multivar-Ω I∗ A∗ x (inv-multivar-Ω I∗ A∗ a) a
    ＝ mul-multivar-Ω I∗ A∗ x (refl-multivar-Ω I A∗)
      by ap (mul-multivar-Ω I∗ A∗ x) (left-inverse-law-mul-multivar-Ω I∗ A∗ a)
    ＝ x
      by right-unit-law-mul-multivar-Ω I∗ A∗ x

  is-retraction-right-mul-inv-multivar-Ω :
    (a : type-multivar-Ω I A∗) →
    is-retraction
      ( λ x → mul-multivar-Ω I∗ A∗ x a)
      ( right-mul-inv-multivar-Ω a)
  is-retraction-right-mul-inv-multivar-Ω a x =
    equational-reasoning
    mul-multivar-Ω I∗ A∗ (mul-multivar-Ω I∗ A∗ x a) (inv-multivar-Ω I∗ A∗ a)
    ＝ mul-multivar-Ω I∗ A∗ x (mul-multivar-Ω I∗ A∗ a (inv-multivar-Ω I∗ A∗ a))
      by associative-mul-multivar-Ω I∗ A∗ x a (inv-multivar-Ω I∗ A∗ a)
    ＝ mul-multivar-Ω I∗ A∗ x (refl-multivar-Ω I A∗)
      by ap (mul-multivar-Ω I∗ A∗ x) (right-inverse-law-mul-multivar-Ω I∗ A∗ a)
    ＝ x
      by right-unit-law-mul-multivar-Ω I∗ A∗ x

  section-right-mul-multivar-Ω :
    (a : type-multivar-Ω I A∗) →
    section (λ x → mul-multivar-Ω I∗ A∗ x a)
  section-right-mul-multivar-Ω a =
    ( right-mul-inv-multivar-Ω a ,
      is-section-right-mul-inv-multivar-Ω a)

  retraction-right-mul-multivar-Ω :
    (a : type-multivar-Ω I A∗) →
    retraction (λ x → mul-multivar-Ω I∗ A∗ x a)
  retraction-right-mul-multivar-Ω a =
    ( right-mul-inv-multivar-Ω a ,
      is-retraction-right-mul-inv-multivar-Ω a)

  is-equiv-right-mul-multivar-Ω :
    (a : type-multivar-Ω I A∗) →
    is-equiv (λ x → mul-multivar-Ω I∗ A∗ x a)
  is-equiv-right-mul-multivar-Ω a =
    is-equiv-is-invertible
      ( right-mul-inv-multivar-Ω a)
      ( is-section-right-mul-inv-multivar-Ω a)
      ( is-retraction-right-mul-inv-multivar-Ω a)

  equiv-right-mul-multivar-Ω :
    (a : type-multivar-Ω I A∗) → type-multivar-Ω I A∗ ≃ type-multivar-Ω I A∗
  equiv-right-mul-multivar-Ω a =
    ((λ x → mul-multivar-Ω I∗ A∗ x a) , is-equiv-right-mul-multivar-Ω a)
```

### `I+1`-ary loops

`(I + 1)`-ary loops are equivalent to families `I → ΩA`, where `Ω` is the
standard loop type.

```agda
module _
  {l1 l2 : Level} {I : UU l1} (A∗ : Pointed-Type l1)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  equiv-type-isolated-point-multivar-Ω :
    type-multivar-Ω (I + unit) A∗ ≃ (I → type-Ω A∗)
  equiv-type-isolated-point-multivar-Ω =
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

For every type $I$ we have the equivalence

$$Ω_{ΣI}(A) ≃ Ω_I(Ω(A)).$$

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A∗ : Pointed-Type l2)
  (let A = type-Pointed-Type A∗) (let a∗ = point-Pointed-Type A∗)
  where

  compute-type-multivar-Ω-suspension :
    type-multivar-Ω (suspension I) A∗ ≃ type-multivar-Ω I (Ω A∗)
  compute-type-multivar-Ω-suspension =
    equivalence-reasoning
    Σ A (λ a → suspension I → a ＝ a∗)
    ≃ Σ A (λ a → Σ (a ＝ a∗) (λ S → Σ (a ＝ a∗) (λ N → I → N ＝ S)))
      by equiv-tot (λ a → equiv-left-swap-Σ ∘e equiv-up-suspension)
    ≃ Σ (Σ A (λ a → a ＝ a∗)) (λ (a , S) → Σ (a ＝ a∗) (λ N → I → N ＝ S))
      by inv-associative-Σ
    ≃ Σ (a∗ ＝ a∗) (λ N → I → N ＝ refl)
      by left-unit-law-Σ-is-contr (is-torsorial-Id' a∗) (a∗ , refl-Ω A∗)
```
