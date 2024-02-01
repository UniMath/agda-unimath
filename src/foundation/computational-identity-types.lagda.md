# Computational identity types

```agda
module foundation.computational-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.judgmentally-compositional-identity-types
open import foundation.judgmentally-right-unital-concatenation-identifications
open import foundation.multivariable-homotopies
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The [standard definition of identity types](foundation-core.identity-types.md)
suffer the limitation that many of the basic operations only satisfy algebraic
laws _weakly_.

In this file, we consider the
{{#concept "computational identity types" Agda=computational-Id}}

```text
  (x ＝ʲ y) := Σ (z : A) ((z ＝ᶜ y) × (z ＝ᶜ x))
```

where `x ＝ᶜ y` is the
[judgmentally compositional identity type](foundation.judgmentally-compositional-identity-types.md)

```text
  (x ＝ᶜ y) := (z : A) → (z ＝ x) → (z ＝ y)
```

This type family is [equivalent](foundation-core.equivalences.md) to the
standard identity types, but is computational and compositional, meaning all the
laws

```text
  inv (inv p) ＝ p
```

judgmentally.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  computational-Id : (x y : A) → UU l
  computational-Id x y = Σ A (λ z → (z ＝ᶜ y) × (z ＝ᶜ x))

  infix 6 _＝ʲ_
  _＝ʲ_ : A → A → UU l
  (a ＝ʲ b) = computational-Id a b

  refl-computational-Id : {x : A} → x ＝ʲ x
  refl-computational-Id {x} =
    (x , refl-compositional-Id , refl-compositional-Id)
```

## Properties

### The computational identity types are equivalent to the standard identity types

In fact, the [retraction](foundation-core.retractions.md) is judgmental, and the
equivalence preserves the groupoid structure.

```agda
module _
  {l : Level} {A : UU l}
  where

  computational-eq-eq : {x y : A} → x ＝ y → x ＝ʲ y
  computational-eq-eq {x} p =
    ( x , compositional-eq-eq p , refl-compositional-Id)

  eq-computational-eq : {x y : A} → x ＝ʲ y → x ＝ y
  eq-computational-eq (z , p , q) =
    eq-compositional-eq (inv-compositional-Id q ∙ᶜ p)

  is-retraction-eq-computational-eq :
    {x y : A} → is-retraction computational-eq-eq (eq-computational-eq {x} {y})
  is-retraction-eq-computational-eq p = left-unit-concatr

  is-section-eq-computational-eq :
    {x y : A} →
    is-section computational-eq-eq (eq-computational-eq {x} {y})
  is-section-eq-computational-eq (z , p , q) =
    ind-compositional-Id
      ( λ _ q →
        computational-eq-eq (eq-computational-eq (z , p , q)) ＝ (z , p , q))
      ( eq-pair-eq-pr2 (eq-pair (is-section-eq-compositional-eq p) refl))
      ( q)

  is-equiv-computational-eq-eq :
    {x y : A} → is-equiv (computational-eq-eq {x} {y})
  pr1 (pr1 is-equiv-computational-eq-eq) = eq-computational-eq
  pr2 (pr1 is-equiv-computational-eq-eq) = is-section-eq-computational-eq
  pr1 (pr2 is-equiv-computational-eq-eq) = eq-computational-eq
  pr2 (pr2 is-equiv-computational-eq-eq) = is-retraction-eq-computational-eq

  is-equiv-eq-computational-eq :
    {x y : A} → is-equiv (eq-computational-eq {x} {y})
  pr1 (pr1 is-equiv-eq-computational-eq) = computational-eq-eq
  pr2 (pr1 is-equiv-eq-computational-eq) = is-retraction-eq-computational-eq
  pr1 (pr2 is-equiv-eq-computational-eq) = computational-eq-eq
  pr2 (pr2 is-equiv-eq-computational-eq) = is-section-eq-computational-eq

  equiv-computational-eq-eq : {x y : A} → (x ＝ y) ≃ (x ＝ʲ y)
  pr1 equiv-computational-eq-eq = computational-eq-eq
  pr2 equiv-computational-eq-eq = is-equiv-computational-eq-eq

  equiv-eq-computational-eq : {x y : A} → (x ＝ʲ y) ≃ (x ＝ y)
  pr1 equiv-eq-computational-eq = eq-computational-eq
  pr2 equiv-eq-computational-eq = is-equiv-eq-computational-eq
```

The reflexivities are mapped to the reflexivities judgementally.

```agda
module _
  {l : Level} {A : UU l}
  where

  computational-eq-eq-refl :
    {x : A} → computational-eq-eq (refl {x = x}) ＝ refl-computational-Id
  computational-eq-eq-refl = refl

  eq-computational-eq-refl :
    {x : A} → eq-computational-eq (refl-computational-Id {x = x}) ＝ refl
  eq-computational-eq-refl = refl
```

### The induction principle for computational identity types

The judgementally computational identity types satisfy the induction principle
of the identity types. This states that given a base point `x : A` and a family
of types over the identity types based at `x`,
`B : (y : A) (p : x ＝ʲ y) → UU l2`, then to construct a dependent function
`f : (y : A) (p : x ＝ʲ y) → B y p` it suffices to define it at
`f x refl-computational-Id`.

**Note.** The only reason we must apply
[function extensionality](foundation.function-extensionality.md) is to show
uniqueness of the induction principle up to _equality_.

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-computational-Id : is-torsorial (computational-Id x)
  is-torsorial-computational-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-computational-eq {x = x} {y}))
      ( is-torsorial-Id x)

  dependent-universal-property-identity-system-computational-Id :
    dependent-universal-property-identity-system
      ( computational-Id x)
      ( refl-computational-Id)
  dependent-universal-property-identity-system-computational-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( refl-computational-Id)
      ( is-torsorial-computational-Id)

module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (p : x ＝ʲ y) → UU l2)
  where

  ind-computational-Id :
    (b : B x refl-computational-Id) {y : A} (p : x ＝ʲ y) → B y p
  ind-computational-Id b {y} =
    map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)
      ( b)
      ( y)

  compute-ind-computational-Id :
    (b : B x refl-computational-Id) →
    ind-computational-Id b refl-computational-Id ＝ b
  compute-ind-computational-Id =
    is-section-map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)

  uniqueness-ind-computational-Id :
    (b : (y : A) (p : x ＝ʲ y) → B y p) →
    (λ y → ind-computational-Id (b x refl-computational-Id) {y}) ＝ b
  uniqueness-ind-computational-Id =
    is-retraction-map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)
```

## Structure

The computational identity types form a groupoidal structure on types. This
structure satisfies the following algebraic laws strictly

- `inv refl ＝ refl`
- `inv (inv p) ＝ p`
- `(p ∙ q) ∙ r ＝ p ∙ (q ∙ r)`
- `refl ∙ p ＝ p` or `p ∙ refl ＝ p`

but not

- `refl ∙ p ＝ p` and `p ∙ refl ＝ p` simultaneously
- `inv p ∙ p ＝ refl`
- `p ∙ inv p ＝ refl`.

### Inverting computational identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-computational-Id : {x y : A} → x ＝ʲ y → y ＝ʲ x
  inv-computational-Id (z , p , q) = (z , q , p)

  compute-inv-computational-Id-refl :
    {x : A} →
    inv-computational-Id (refl-computational-Id {x = x}) ＝ refl-computational-Id
  compute-inv-computational-Id-refl = refl

  inv-inv-computational-Id :
    {x y : A} (p : x ＝ʲ y) → inv-computational-Id (inv-computational-Id p) ＝ p
  inv-inv-computational-Id p = refl
```

The inversion operation corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  commutative-inv-computational-eq-eq :
    (p : x ＝ y) →
    computational-eq-eq (inv p) ＝ inv-computational-Id (computational-eq-eq p)
  commutative-inv-computational-eq-eq refl = refl

  -- commutative-inv-eq-computational-eq :
  --   (p : x ＝ʲ y) →
  --   eq-computational-eq (inv-computational-Id p) ＝ inv (eq-computational-eq p)
  -- commutative-inv-eq-computational-eq (z , f , g) =
  --   equational-reasoning g y (refl ∙ᵣ inv (f z refl)) ＝ inv (f x (refl ∙ᵣ inv (g z refl))) by {!   !}
```

### The concatenation operations on computational identifications

There is both a judgmentally left unital concatenation operation and a
judgmentally right unital concatenation operation, although both are
judgmentally associative.

**Note.** Since they are judgmentally associative, the only instances where they
will not reduce is thus when the reflexivity appears all the way to the right,
or all the way to the left in a string of concatenations respectively.

#### The judgmentally left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ₗʲ_
  _∙ₗʲ_ : {x y z : A} → x ＝ʲ y → y ＝ʲ z → x ＝ʲ z
  (z , p , q) ∙ₗʲ (z' , p' , q') =
    (z' , p' , q' ∙ᶜ invr-compositional-Id p ∙ᶜ q)

  concatl-computational-Id : {x y : A} → x ＝ʲ y → (z : A) → y ＝ʲ z → x ＝ʲ z
  concatl-computational-Id p z q = p ∙ₗʲ q

  concatl-computational-Id' : (x : A) {y z : A} → y ＝ʲ z → x ＝ʲ y → x ＝ʲ z
  concatl-computational-Id' x q p = p ∙ₗʲ q
```

#### The judgmentally left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ᵣʲ_
  _∙ᵣʲ_ : {x y z : A} → x ＝ʲ y → y ＝ʲ z → x ＝ʲ z
  (w , p , q) ∙ᵣʲ (w' , p' , q') =
    (w , p ∙ᶜ invr-compositional-Id q' ∙ᶜ p' , q)

  concatr-computational-Id : {x y : A} → x ＝ʲ y → (z : A) → y ＝ʲ z → x ＝ʲ z
  concatr-computational-Id p z q = p ∙ᵣʲ q

  concatr-computational-Id' : (x : A) {y z : A} → y ＝ʲ z → x ＝ʲ y → x ＝ʲ z
  concatr-computational-Id' x q p = p ∙ᵣʲ q
```

### The groupoidal laws for the computational identity types

#### The groupoidal laws for the judgmentally left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  assoc-concatl-computational-Id :
    (p : x ＝ʲ y) (q : y ＝ʲ z) (r : z ＝ʲ w) →
    (p ∙ₗʲ q) ∙ₗʲ r ＝ p ∙ₗʲ (q ∙ₗʲ r)
  assoc-concatl-computational-Id p q r = refl

module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-concatl-computational-Id :
    {p : x ＝ʲ y} → refl-computational-Id ∙ₗʲ p ＝ p
  left-unit-concatl-computational-Id = refl

  right-unit-concatl-computational-Id :
    {p : x ＝ʲ y} → p ∙ₗʲ refl-computational-Id ＝ p
  right-unit-concatl-computational-Id {z , p , q} =
    ind-compositional-Id
      ( λ _ p → (z , p , q) ∙ₗʲ refl-computational-Id ＝ (z , p , q))
      ( refl)
      ( p)

  left-inv-concatl-computational-Id :
    (p : x ＝ʲ y) → inv-computational-Id p ∙ₗʲ p ＝ refl-computational-Id
  left-inv-concatl-computational-Id (z , p , q) =
    ind-compositional-Id
      ( λ _ p →
        ( inv-computational-Id (z , p , q) ∙ₗʲ (z , p , q)) ＝
        ( refl-computational-Id))
      ( eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-compositional-Id q)))
      ( p)

  right-inv-concatl-computational-Id :
    (p : x ＝ʲ y) → p ∙ₗʲ inv-computational-Id p ＝ refl-computational-Id
  right-inv-concatl-computational-Id (z , p , q) =
    ind-compositional-Id
      ( λ _ q →
        ( (z , p , q) ∙ₗʲ inv-computational-Id (z , p , q)) ＝
        ( refl-computational-Id))
      ( eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-compositional-Id p)))
      ( q)

  -- distributive-inv-concatl-computational-Id :
  --   {x y : A} (p : x ＝ʲ y) {z : A} (q : y ＝ʲ z) →
  --   inv-computational-Id (p ∙ₗʲ q) ＝ inv-computational-Id q ∙ₗʲ inv-computational-Id p
  -- distributive-inv-concatl-computational-Id (z , refl , refl) (z' , p' , refl) =
  --   eq-pair-eq-pr2 (eq-pair-eq-pr2 (inv left-unit-concatr))
```

#### The groupoidal laws for the judgmentally right unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc-concatr-computational-Id :
    {x y z w : A} (p : x ＝ʲ y) (q : y ＝ʲ z) (r : z ＝ʲ w) →
    (p ∙ᵣʲ q) ∙ᵣʲ r ＝ p ∙ᵣʲ (q ∙ᵣʲ r)
  assoc-concatr-computational-Id p q r = refl

  left-unit-concatr-computational-Id :
    {x y : A} {p : x ＝ʲ y} → refl-computational-Id ∙ᵣʲ p ＝ p
  left-unit-concatr-computational-Id {x} {y} {z , p , q} =
    ind-compositional-Id
      ( λ w q → refl-computational-Id ∙ᵣʲ (z , p , q) ＝ (z , p , q))
      ( refl)
      ( q)

  right-unit-concatr-computational-Id :
    {x y : A} {p : x ＝ʲ y} → p ∙ᵣʲ refl-computational-Id ＝ p
  right-unit-concatr-computational-Id = refl
```

## References

- <https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ>
