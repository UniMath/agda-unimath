# Yoneda identity types

```agda
module foundation.yoneda-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.multivariable-homotopies
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The standard definition of [identity types](foundation-core.identity-types.md)
has the limitation that many of the basic operations only satisfy algebraic laws
_weakly_. On this page, we consider the
{{#concept "Yoneda identity types" Agda=yoneda-Id}}

```text
  (x ＝ʸ y) := (z : A) → (z ＝ x) → (z ＝ y)
```

Through the interpretation of types as ∞-categories, where the hom-space
`hom(x , y)` is defined to be the identity type `x ＝ y`, we may observe that
this is an instance of the Yoneda embedding. We use a superscript `y` in the
notation of the Yoneda identity types, and similarly we call elements of the
Yoneda identity types for {{#concept "Yoneda identifications" Agda=yoneda-Id}}.

The Yoneda identity types are [equivalent](foundation-core.equivalences.md) to
the standard identity types, but satisfy strict laws

- `(p ∙ʸ q) ∙ʸ r ≐ p ∙ʸ (q ∙ʸ r)`,
- `reflʸ ∙ʸ p ≐ p`, and
- `p ∙ʸ reflʸ ≐ p`.

This is achieved by proxying to function composition and utilizing its
computational properties, and relies heavily on the
[function extensionality axiom](foundation.function-extensionality.md). More
concretely, the reflexivity is given by the identity function, and path
concatenation is given by function composition.

In addition to these strictness laws, we can make the type satisfy the strict
law `inv reflʸ ≐ reflʸ`. Moreover, while the induction principle of the Yoneda
identity types does not in general satisfy the computation rule strictly, we can
define its recursion principle such that does.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  yoneda-Id : (x y : A) → UU l
  yoneda-Id x y = (z : A) → z ＝ x → z ＝ y

  infix 6 _＝ʸ_
  _＝ʸ_ : A → A → UU l
  (a ＝ʸ b) = yoneda-Id a b
```

We define the reflexivity by the identity function:

```agda
  reflʸ : {x : A} → x ＝ʸ x
  reflʸ z = id
```

## Properties

### Elements of the Yoneda identity type act like postconcatenation operations

The following is a collection of properties of Yoneda identifications similar to
properties of the postconcatenation operation of identifications.

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-preconcat-Id-yoneda-Id :
    {x y z w : A} (f : x ＝ʸ y) (p : w ＝ z) (q : z ＝ x) →
    f w (p ∙ q) ＝ p ∙ f z q
  commutative-preconcat-Id-yoneda-Id f refl q = refl

  commutative-preconcat-refl-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (q : z ＝ x) → f z q ＝ q ∙ f x refl
  commutative-preconcat-refl-Id-yoneda-Id {z = z} f q =
    ap (f z) (inv right-unit) ∙ commutative-preconcat-Id-yoneda-Id f q refl

  commutative-preconcatr-Id-yoneda-Id :
    {x y z w : A} (f : x ＝ʸ y) (p : w ＝ z) (q : z ＝ x) →
    f w (p ∙ᵣ q) ＝ p ∙ᵣ f z q
  commutative-preconcatr-Id-yoneda-Id {x} {y} {z} {w} f p q =
    ( ap (f w) (eq-concat-right-strict-concat p q)) ∙
    ( commutative-preconcat-Id-yoneda-Id f p q) ∙
    ( eq-right-strict-concat-concat p (f z q))

  commutative-preconcatr-refl-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (q : z ＝ x) → f z q ＝ q ∙ᵣ f x refl
  commutative-preconcatr-refl-Id-yoneda-Id f q =
    commutative-preconcatr-Id-yoneda-Id f q refl

  compute-inv-Id-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) → f y (inv (f x refl)) ＝ refl
  compute-inv-Id-yoneda-Id {x} f =
    ( commutative-preconcat-refl-Id-yoneda-Id f (inv (f x refl))) ∙
    ( left-inv (f x refl))

  inv-distributive-inv-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (g : x ＝ʸ z) →
    inv (g y (inv (f x refl))) ＝ f z (inv (g x refl))
  inv-distributive-inv-Id-yoneda-Id {x} f g =
    ( ap inv (commutative-preconcat-refl-Id-yoneda-Id g (inv (f x refl)))) ∙
    ( distributive-inv-concat (inv (f x refl)) (g x refl)) ∙
    ( ap (inv (g x refl) ∙_) (inv-inv (f x refl))) ∙
    ( inv (commutative-preconcat-refl-Id-yoneda-Id f (inv (g x refl))))

  distributive-inv-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (g : x ＝ʸ z) →
    f z (inv (g x refl)) ＝ inv (g y (inv (f x refl)))
  distributive-inv-Id-yoneda-Id f g =
    inv (inv-distributive-inv-Id-yoneda-Id f g)
```

### The Yoneda identity types are equivalent to the standard identity types

The equivalence `(x ＝ y) ≃ (x ＝ʸ y)` is defined from left to right by the
postconcatenation operation

```text
  yoneda-eq-eq := p ↦ (q ↦ q ∙ p)   : x ＝ y → x ＝ʸ y,
```

and from right to left by evaluation at the reflexivity

```text
  eq-yoneda-eq := f ↦ f refl   : x ＝ʸ y → x ＝ y.
```

It should be noted that we define the map `x ＝ y → x ＝ʸ y` using the
[strictly right unital concatenation operation](foundation.strictly-right-unital-concatenation-identifications.md).
While this obstructs us from showing that the
[homotopy](foundation-core.homotopies.md) `eq-yoneda-eq ∘ yoneda-eq-eq ~ id`
holds by reflexivity as demonstrated by the computation

```text
  eq-yoneda-eq ∘ yoneda-eq-eq
  ≐ p ↦ (f ↦ f refl) (q ↦ q ∙ p)
  ≐ p ↦ ((q ↦ q ∙ p) refl)
  ≐ p ↦ refl ∙ p,
```

it allows us to show that reflexivities are preserved strictly in both
directions, and not just from `x ＝ʸ y` to `x ＝ y`.

From left to right:

```text
  yoneda-eq-eq refl ≐ (p ↦ (q ↦ q ∙ p)) refl ≐ (q ↦ q ∙ refl) ≐ (q ↦ q) ≐ reflʸ
```

and from right to left:

```text
  eq-yoneda-eq reflʸ ≐ (f ↦ f refl) reflʸ ≐ (q ↦ q) refl ≐ refl.
```

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  yoneda-eq-eq : x ＝ y → x ＝ʸ y
  yoneda-eq-eq p z q = q ∙ᵣ p

  eq-yoneda-eq : x ＝ʸ y → x ＝ y
  eq-yoneda-eq f = f x refl
```

The construction of the homotopy `yoneda-eq-eq ∘ eq-yoneda-eq ~ id` requires the
[function extensionality axiom](foundation.function-extensionality.md). And
while we could show an analogous induction principle of the Yoneda identity
types without the use of this axiom, function extensionality will become
indispensable regardless when we proceed to proving miscellaneous algebraic laws
of the Yoneda identity type.

```agda
  is-section-eq-yoneda-eq :
    is-section yoneda-eq-eq eq-yoneda-eq
  is-section-eq-yoneda-eq f =
    eq-multivariable-htpy 2
      ( λ _ p → inv (commutative-preconcatr-refl-Id-yoneda-Id f p))

  is-retraction-eq-yoneda-eq :
    is-retraction yoneda-eq-eq eq-yoneda-eq
  is-retraction-eq-yoneda-eq p = left-unit-right-strict-concat

  is-equiv-yoneda-eq-eq : is-equiv yoneda-eq-eq
  pr1 (pr1 is-equiv-yoneda-eq-eq) = eq-yoneda-eq
  pr2 (pr1 is-equiv-yoneda-eq-eq) = is-section-eq-yoneda-eq
  pr1 (pr2 is-equiv-yoneda-eq-eq) = eq-yoneda-eq
  pr2 (pr2 is-equiv-yoneda-eq-eq) = is-retraction-eq-yoneda-eq

  is-equiv-eq-yoneda-eq : is-equiv eq-yoneda-eq
  pr1 (pr1 is-equiv-eq-yoneda-eq) = yoneda-eq-eq
  pr2 (pr1 is-equiv-eq-yoneda-eq) = is-retraction-eq-yoneda-eq
  pr1 (pr2 is-equiv-eq-yoneda-eq) = yoneda-eq-eq
  pr2 (pr2 is-equiv-eq-yoneda-eq) = is-section-eq-yoneda-eq

  equiv-yoneda-eq-eq : (x ＝ y) ≃ (x ＝ʸ y)
  pr1 equiv-yoneda-eq-eq = yoneda-eq-eq
  pr2 equiv-yoneda-eq-eq = is-equiv-yoneda-eq-eq

  equiv-eq-yoneda-eq : (x ＝ʸ y) ≃ (x ＝ y)
  pr1 equiv-eq-yoneda-eq = eq-yoneda-eq
  pr2 equiv-eq-yoneda-eq = is-equiv-eq-yoneda-eq
```

This equvialence preserves the reflexivity elements strictly in both directions.

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-section-eq-yoneda-eq-refl :
    yoneda-eq-eq (eq-yoneda-eq (reflʸ {x = x})) ＝ reflʸ
  is-section-eq-yoneda-eq-refl = refl

  preserves-refl-yoneda-eq-eq :
    yoneda-eq-eq (refl {x = x}) ＝ reflʸ
  preserves-refl-yoneda-eq-eq = refl

  preserves-refl-eq-yoneda-eq :
    eq-yoneda-eq (reflʸ {x = x}) ＝ refl
  preserves-refl-eq-yoneda-eq = refl
```

Below, we consider the alternative definition of `yoneda-eq-eq` using the
strictly left unital concatenation operation on standard identity types. As we
can see, the retracting homotopy holds strictly, but now `yoneda-eq-eq refl`
does not compute strictly to `reflʸ`.

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  yoneda-eq-eq' : x ＝ y → x ＝ʸ y
  yoneda-eq-eq' p z q = q ∙ p

  is-section-eq-yoneda-eq' :
    is-section yoneda-eq-eq' eq-yoneda-eq
  is-section-eq-yoneda-eq' f =
    eq-multivariable-htpy 2
      ( λ _ p → inv (commutative-preconcat-refl-Id-yoneda-Id f p))

  is-retraction-eq-yoneda-eq' :
    is-retraction yoneda-eq-eq' eq-yoneda-eq
  is-retraction-eq-yoneda-eq' p = refl

module _
  {l : Level} {A : UU l}
  where

  preserves-refl-yoneda-eq-eq' :
    {x : A} → yoneda-eq-eq' (refl {x = x}) ＝ reflʸ
  preserves-refl-yoneda-eq-eq' =
    eq-multivariable-htpy 2 (λ _ p → right-unit)
```

### Torsoriality of the Yoneda identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-yoneda-Id : is-torsorial (yoneda-Id x)
  is-torsorial-yoneda-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-yoneda-eq {x = x} {y}))
      ( is-torsorial-Id x)
```

### The dependent universal property of the Yoneda identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  dependent-universal-property-identity-system-yoneda-Id :
    dependent-universal-property-identity-system
      ( yoneda-Id x)
      ( reflʸ)
  dependent-universal-property-identity-system-yoneda-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( reflʸ)
      ( is-torsorial-yoneda-Id)
```

### The induction principle for the Yoneda identity types

The Yoneda identity types satisfy the induction principle of the identity types.
This states that given a base point `x : A` and a family of types over the
identity types based at `x`, `B : (y : A) (f : x ＝ʸ y) → UU l2`, then to
construct a dependent function `g : (y : A) (f : x ＝ʸ y) → B y p` it suffices
to define it at `g x reflʸ`.

**Note.** As stated before, a drawback of the Yoneda identity types is that they
do not satisfy a strict computation rule for this induction principle.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (f : x ＝ʸ y) → UU l2)
  where

  ind-yoneda-Id' :
    (b : B x reflʸ) {y : A} (f : x ＝ʸ y) → B y f
  ind-yoneda-Id' b {y} =
    map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)
      ( b)
      ( y)

  compute-ind-yoneda-Id' :
    (b : B x reflʸ) →
    ind-yoneda-Id' b reflʸ ＝ b
  compute-ind-yoneda-Id' =
    is-section-map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)

  uniqueness-ind-yoneda-Id' :
    (b : (y : A) (f : x ＝ʸ y) → B y f) →
    (λ y → ind-yoneda-Id' (b x reflʸ) {y}) ＝ b
  uniqueness-ind-yoneda-Id' =
    is-retraction-map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)
```

The following is a more concrete construction of the induction principle. We
observe that while `eq-yoneda-eq` and `yoneda-eq-eq` preserve reflexivities
strictly as required, the reduction is obstructed because the proof of
`is-section-eq-yoneda-eq` does not reduce to `refl` when `f ≐ reflʸ`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (f : x ＝ʸ y) → UU l2)
  where

  ind-yoneda-Id :
    (b : B x reflʸ) {y : A} (f : x ＝ʸ y) → B y f
  ind-yoneda-Id b {y} f =
    tr
      ( B y)
      ( is-section-eq-yoneda-eq f)
      ( ind-Id x (λ y p → B y (yoneda-eq-eq p)) b y (eq-yoneda-eq f))
```

While the induction principle does not have the desired reduction behaviour, the
nondependent eliminator does. This is simply because we no longer need to
[transport](foundation-core.transport-along-identifications.md) along
`is-section-eq-yoneda-eq`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  {B : A → UU l2}
  where

  rec-yoneda-Id :
    (b : B x) {y : A} → x ＝ʸ y → B y
  rec-yoneda-Id b f = tr B (eq-yoneda-eq f) b

  compute-rec-yoneda-Id :
    (b : B x) → rec-yoneda-Id b reflʸ ＝ b
  compute-rec-yoneda-Id b = refl

  uniqueness-rec-yoneda-Id :
    (b : (y : A) → x ＝ʸ y → B y) →
    (λ y → rec-yoneda-Id (b x reflʸ) {y}) ＝ b
  uniqueness-rec-yoneda-Id b =
    ( inv
      ( uniqueness-ind-yoneda-Id'
        ( λ y _ → B y)
        ( λ y → rec-yoneda-Id (b x reflʸ)))) ∙
    ( uniqueness-ind-yoneda-Id' (λ y _ → B y) b)
```

## Structure

The Yoneda identity types form a strictly compositional weak groupoidal
structure on types.

### Inverting Yoneda identifications

We consider two ways of defining the inversion operation on Yoneda
identifications: by the strictly right unital, and strictly left unital
concatenation operation on the underlying identity type respectively. In
contrast to the latter, the former enjoys the computational property

```text
  inv reflʸ ≐ reflʸ,
```

hence it will be preferred going forward.

#### The inversion operation defined by the strictly right unital concatenation operation on identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-yoneda-Id : {x y : A} → x ＝ʸ y → y ＝ʸ x
  inv-yoneda-Id {x} f z p = p ∙ᵣ inv (f x refl)

  compute-inv-yoneda-Id-refl :
    {x : A} →
    inv-yoneda-Id (reflʸ {x = x}) ＝ reflʸ
  compute-inv-yoneda-Id-refl = refl

  inv-inv-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) →
    inv-yoneda-Id (inv-yoneda-Id f) ＝ f
  inv-inv-yoneda-Id {x} f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( p ∙ᵣ_)
          ( ap inv left-unit-right-strict-concat ∙ inv-inv (f x refl))) ∙
        ( inv (commutative-preconcatr-refl-Id-yoneda-Id f p)))
```

The inversion operation corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-inv-yoneda-eq-eq' :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ inv-yoneda-Id (yoneda-eq-eq' p)
  preserves-inv-yoneda-eq-eq' p = refl

  preserves-inv-yoneda-eq-eq :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ inv-yoneda-Id (yoneda-eq-eq p)
  preserves-inv-yoneda-eq-eq p =
    eq-multivariable-htpy 2
      ( λ _ q → ap (λ r → q ∙ᵣ inv r) (inv left-unit-right-strict-concat))

  preserves-inv-eq-yoneda-eq :
    {x y : A} (f : x ＝ʸ y) →
    eq-yoneda-eq (inv-yoneda-Id f) ＝ inv (eq-yoneda-eq f)
  preserves-inv-eq-yoneda-eq f = left-unit-right-strict-concat
```

#### The inversion operation defined by the strictly left unital concatenation operation on identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  left-strict-inv-yoneda-Id : {x y : A} → x ＝ʸ y → y ＝ʸ x
  left-strict-inv-yoneda-Id {x} f z p = p ∙ inv (f x refl)

  compute-left-strict-inv-yoneda-Id-refl :
    {x : A} → left-strict-inv-yoneda-Id (reflʸ {x = x}) ＝ reflʸ
  compute-left-strict-inv-yoneda-Id-refl =
    eq-multivariable-htpy 2 (λ _ p → right-unit)

  left-strict-inv-left-strict-inv-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) →
    left-strict-inv-yoneda-Id (left-strict-inv-yoneda-Id f) ＝ f
  left-strict-inv-left-strict-inv-yoneda-Id {x} f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap (p ∙_) (inv-inv (f x refl))) ∙
        ( inv (commutative-preconcat-refl-Id-yoneda-Id f p)))
```

This inversion operation also corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-left-strict-inv-yoneda-eq-eq :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ left-strict-inv-yoneda-Id (yoneda-eq-eq p)
  preserves-left-strict-inv-yoneda-eq-eq p =
    eq-multivariable-htpy 2
      ( λ _ q →
        ( eq-concat-right-strict-concat q (inv p)) ∙
        ( ap (λ r → q ∙ inv r) (inv left-unit-right-strict-concat)))

  preserves-left-strict-inv-eq-yoneda-eq :
    {x y : A} (f : x ＝ʸ y) →
    eq-yoneda-eq (left-strict-inv-yoneda-Id f) ＝ inv (eq-yoneda-eq f)
  preserves-left-strict-inv-eq-yoneda-eq f = refl
```

### Concatenation of Yoneda identifications

The concatenation operation on Yoneda identifications is defined by function
composition

```text
  f ∙ʸ g := z p ↦ g z (f z p)
```

and is thus strictly associative and two-sided unital (since the reflexivities
are given by the identity functions).

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ʸ_
  _∙ʸ_ : {x y z : A} → x ＝ʸ y → y ＝ʸ z → x ＝ʸ z
  (f ∙ʸ g) z p = g z (f z p)

  concat-yoneda-Id : {x y : A} → x ＝ʸ y → (z : A) → y ＝ʸ z → x ＝ʸ z
  concat-yoneda-Id f z g = f ∙ʸ g

  concat-yoneda-Id' : (x : A) {y z : A} → y ＝ʸ z → x ＝ʸ y → x ＝ʸ z
  concat-yoneda-Id' x g f = f ∙ʸ g
```

The concatenation operation corresponds to the standard concatenation operation
on identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-concat-yoneda-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    yoneda-eq-eq (p ∙ q) ＝ yoneda-eq-eq p ∙ʸ yoneda-eq-eq q
  preserves-concat-yoneda-eq-eq refl refl = refl

  preserves-concat-eq-yoneda-eq :
    {x y z : A} (f : x ＝ʸ y) (g : y ＝ʸ z) →
    eq-yoneda-eq (f ∙ʸ g) ＝ eq-yoneda-eq f ∙ eq-yoneda-eq g
  preserves-concat-eq-yoneda-eq {x} f g =
    commutative-preconcat-refl-Id-yoneda-Id g (f x refl)
```

### The groupoidal laws for the Yoneda identity types

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  assoc-yoneda-Id :
    (f : x ＝ʸ y) {z w : A} (g : y ＝ʸ z) (h : z ＝ʸ w) →
    (f ∙ʸ g) ∙ʸ h ＝ f ∙ʸ (g ∙ʸ h)
  assoc-yoneda-Id f g h = refl

  left-unit-yoneda-Id :
    {f : x ＝ʸ y} → reflʸ ∙ʸ f ＝ f
  left-unit-yoneda-Id = refl

  right-unit-yoneda-Id :
    {f : x ＝ʸ y} → f ∙ʸ reflʸ ＝ f
  right-unit-yoneda-Id = refl

  left-inv-yoneda-Id :
    (f : x ＝ʸ y) → inv-yoneda-Id f ∙ʸ f ＝ reflʸ
  left-inv-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( commutative-preconcatr-Id-yoneda-Id f p (inv (f x refl))) ∙
        ( ap (p ∙ᵣ_) (compute-inv-Id-yoneda-Id f)))

  left-left-strict-inv-yoneda-Id :
    (f : x ＝ʸ y) → left-strict-inv-yoneda-Id f ∙ʸ f ＝ reflʸ
  left-left-strict-inv-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( commutative-preconcat-Id-yoneda-Id f p (inv (f x refl))) ∙
        ( ap (p ∙_) (compute-inv-Id-yoneda-Id f) ∙ right-unit))

  right-inv-yoneda-Id :
    (f : x ＝ʸ y) → f ∙ʸ inv-yoneda-Id f ＝ reflʸ
  right-inv-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( _∙ᵣ inv (f x refl))
          ( commutative-preconcatr-refl-Id-yoneda-Id f p)) ∙
        ( assoc-right-strict-concat p (f x refl) (inv (f x refl))) ∙
        ( ap (p ∙ᵣ_) (right-inv-right-strict-concat (f x refl))))

  right-left-strict-inv-yoneda-Id :
    (f : x ＝ʸ y) → f ∙ʸ left-strict-inv-yoneda-Id f ＝ reflʸ
  right-left-strict-inv-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( _∙ inv (f x refl))
          ( commutative-preconcat-refl-Id-yoneda-Id f p)) ∙
        ( assoc p (f x refl) (inv (f x refl))) ∙
        ( ap (p ∙_) (right-inv (f x refl))) ∙
        ( right-unit))

  distributive-inv-concat-yoneda-Id :
    (f : x ＝ʸ y) {z : A} (g : y ＝ʸ z) →
    inv-yoneda-Id (f ∙ʸ g) ＝ inv-yoneda-Id g ∙ʸ inv-yoneda-Id f
  distributive-inv-concat-yoneda-Id f g =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( p ∙ᵣ_)
          ( ( ap
              ( inv)
              ( commutative-preconcatr-refl-Id-yoneda-Id g (f x refl))) ∙
            ( distributive-inv-right-strict-concat (f x refl) (g y refl)))) ∙
          ( inv
            ( assoc-right-strict-concat p (inv (g y refl)) (inv (f x refl)))))

  distributive-left-strict-inv-concat-yoneda-Id :
    (f : x ＝ʸ y) {z : A} (g : y ＝ʸ z) →
    left-strict-inv-yoneda-Id (f ∙ʸ g) ＝
    left-strict-inv-yoneda-Id g ∙ʸ left-strict-inv-yoneda-Id f
  distributive-left-strict-inv-concat-yoneda-Id f g =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( p ∙_)
          ( ( ap
              ( inv)
              ( commutative-preconcat-refl-Id-yoneda-Id g (f x refl))) ∙
            ( distributive-inv-concat (f x refl) (g y refl)))) ∙
        ( inv (assoc p (inv (g y refl)) (inv (f x refl)))))
```

## Operations

We can define a range basic operations on the Yoneda identifications that all
enjoy strict computational properties.

### Action of functions on Yoneda identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  eq-ap-yoneda-Id : {x y : A} → x ＝ʸ y → f x ＝ f y
  eq-ap-yoneda-Id = ap f ∘ eq-yoneda-eq

  ap-yoneda-Id : {x y : A} → x ＝ʸ y → f x ＝ʸ f y
  ap-yoneda-Id = yoneda-eq-eq ∘ eq-ap-yoneda-Id

  compute-ap-reflʸ :
    {x : A} → ap-yoneda-Id (reflʸ {x = x}) ＝ reflʸ
  compute-ap-reflʸ = refl

module _
  {l1 : Level} {A : UU l1}
  where

  compute-ap-id-yoneda-Id :
    {x y : A} (p : x ＝ʸ y) → ap-yoneda-Id id p ＝ p
  compute-ap-id-yoneda-Id {x} p =
    eq-multivariable-htpy 2
      ( λ _ q →
        ( ap (q ∙ᵣ_) (ap-id (p x refl))) ∙
        ( inv (commutative-preconcatr-refl-Id-yoneda-Id p q)))
```

### Transport along Yoneda identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  tr-yoneda-Id : {x y : A} → x ＝ʸ y → B x → B y
  tr-yoneda-Id = tr B ∘ eq-yoneda-eq

  compute-tr-reflʸ :
    {x : A} → tr-yoneda-Id (reflʸ {x = x}) ＝ id
  compute-tr-reflʸ = refl
```

### Function extensionality with respect to Yoneda identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  htpy-yoneda-eq : f ＝ʸ g → f ~ g
  htpy-yoneda-eq = htpy-eq ∘ eq-yoneda-eq

  yoneda-eq-htpy : f ~ g → f ＝ʸ g
  yoneda-eq-htpy = yoneda-eq-eq ∘ eq-htpy

  equiv-htpy-yoneda-eq : (f ＝ʸ g) ≃ (f ~ g)
  equiv-htpy-yoneda-eq = equiv-funext ∘e equiv-eq-yoneda-eq

  equiv-yoneda-eq-htpy : (f ~ g) ≃ (f ＝ʸ g)
  equiv-yoneda-eq-htpy = equiv-yoneda-eq-eq ∘e equiv-eq-htpy

  funext-yoneda-Id : is-equiv htpy-yoneda-eq
  funext-yoneda-Id = is-equiv-map-equiv equiv-htpy-yoneda-eq
```

### Univalence with respect to Yoneda identifications

```agda
module _
  {l1 : Level} {A B : UU l1}
  where

  map-yoneda-eq : A ＝ʸ B → A → B
  map-yoneda-eq = map-eq ∘ eq-yoneda-eq

  equiv-yoneda-eq : A ＝ʸ B → A ≃ B
  equiv-yoneda-eq = equiv-eq ∘ eq-yoneda-eq

  yoneda-eq-equiv : A ≃ B → A ＝ʸ B
  yoneda-eq-equiv = yoneda-eq-eq ∘ eq-equiv

  equiv-equiv-yoneda-eq : (A ＝ʸ B) ≃ (A ≃ B)
  equiv-equiv-yoneda-eq = equiv-univalence ∘e equiv-eq-yoneda-eq

  is-equiv-equiv-yoneda-eq : is-equiv equiv-yoneda-eq
  is-equiv-equiv-yoneda-eq = is-equiv-map-equiv equiv-equiv-yoneda-eq

  equiv-yoneda-eq-equiv : (A ≃ B) ≃ (A ＝ʸ B)
  equiv-yoneda-eq-equiv = equiv-yoneda-eq-eq ∘e equiv-eq-equiv A B

  is-equiv-yoneda-eq-equiv : is-equiv yoneda-eq-equiv
  is-equiv-yoneda-eq-equiv = is-equiv-map-equiv equiv-yoneda-eq-equiv
```

## See also

- [The strictly involutive identity types](foundation.strictly-involutive-identity-types.md)
  for an identity relation that is strictly involutive, and one-sided unital.
- [The computational identity types](foundation.computational-identity-types.md)
  for an identity relation that is strictly involutive, associative, and
  one-sided unital.

## References

- _Definitions of equivalence satisfying judgmental/strict groupoid laws?_ -
  Google groups conversation
  (<https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ>)
