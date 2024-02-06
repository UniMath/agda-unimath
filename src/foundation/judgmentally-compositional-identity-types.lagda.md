# Judgmentally compositional identity types

```agda
module foundation.judgmentally-compositional-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.judgmentally-right-unital-concatenation-identifications
open import foundation.multivariable-homotopies
open import foundation.transport-along-identifications
open import foundation.universal-property-identity-systems
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.univalence
```

</details>

## Idea

The standard definition of [identity types](foundation-core.identity-types.md)
has the limitation that many of the basic operations only satisfy algebraic laws
_weakly_. In this file, we consider the
{{#concept "judgmentally compositional identity types" Agda=yoneda-Id}}

```text
  (x ＝ʸ y) := (z : A) → (z ＝ x) → (z ＝ y)
```

Through the interpretation of types as ∞-categories, we can immediately see that
this is an instance of the Yoneda-embedding.

This type family is [equivalent](foundation-core.equivalences.md) to the
standard identity types, but satisfies the judgmental laws

- `(p ∙ q) ∙ r ≐ p ∙ (q ∙ r)`,
- `refl ∙ p ≐ p`, and
- `p ∙ refl ≐ p`.

This is achieved by proxiyng to function composition and utilizing its
computational properties, and relies heavily on the
[function extensionality axiom](foundation.function-extensionality.md).

In addition, we can make the type satisfy the judgmental law

- `inv refl ≐ refl`, and even
- `rec f refl ≐ f refl`.

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

  refl-yoneda-Id : {x : A} → x ＝ʸ x
  refl-yoneda-Id z = id
```

## Properties

### Elements of the judgmentally compositional identity type act like postconcatenation operations

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-postconcat-Id-yoneda-Id :
    {x y z w : A} (f : x ＝ʸ y) (p : w ＝ z) (q : z ＝ x) →
    f w (p ∙ q) ＝ p ∙ f z q
  commutative-postconcat-Id-yoneda-Id f refl q = refl

  commutative-postconcat-refl-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (q : z ＝ x) → f z q ＝ q ∙ f x refl
  commutative-postconcat-refl-Id-yoneda-Id {z = z} f q =
    ap (f z) (inv right-unit) ∙ commutative-postconcat-Id-yoneda-Id f q refl

  commutative-postconcatr-Id-yoneda-Id :
    {x y z w : A} (f : x ＝ʸ y) (p : w ＝ z) (q : z ＝ x) →
    f w (p ∙ᵣ q) ＝ p ∙ᵣ f z q
  commutative-postconcatr-Id-yoneda-Id {x} {y} {z} {w} f p q =
    ( ap (f w) (eq-concat-concatr p q)) ∙
    ( commutative-postconcat-Id-yoneda-Id f p q) ∙
    ( eq-concatr-concat p (f z q))

  commutative-postconcatr-refl-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (q : z ＝ x) → f z q ＝ q ∙ᵣ f x refl
  commutative-postconcatr-refl-Id-yoneda-Id f q =
    commutative-postconcatr-Id-yoneda-Id f q refl

  compute-inv-Id-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) → f y (inv (f x refl)) ＝ refl
  compute-inv-Id-yoneda-Id {x} f =
    ( commutative-postconcat-refl-Id-yoneda-Id f (inv (f x refl))) ∙
    ( left-inv (f x refl))

  inv-distributive-inv-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (g : x ＝ʸ z) →
    inv (g y (inv (f x refl))) ＝ f z (inv (g x refl))
  inv-distributive-inv-Id-yoneda-Id {x} {y} f g =
    ( ap inv (commutative-postconcat-refl-Id-yoneda-Id g (inv (f x refl)))) ∙
    ( distributive-inv-concat (inv (f x refl)) (g x refl)) ∙
    ( ap (inv (g x refl) ∙_) (inv-inv (f x refl))) ∙
    ( inv (commutative-postconcat-refl-Id-yoneda-Id f (inv (g x refl))))

  distributive-inv-Id-yoneda-Id :
    {x y z : A} (f : x ＝ʸ y) (g : x ＝ʸ z) →
    f z (inv (g x refl)) ＝ inv (g y (inv (f x refl)))
  distributive-inv-Id-yoneda-Id f g =
    inv (inv-distributive-inv-Id-yoneda-Id f g)
```

### The judgmentally compositional identity types are equivalent to the standard identity types

We define the equivalence `yoneda-eq-eq : x ＝ y → x ＝ʸ y` using the
judgmentally right unital concatenation operation on identifications. This gives
us the judgmental computation rules

```text
  yoneda-eq-eq refl ≐ refl-yoneda-Id
```

and

```text
  eq-yoneda-eq refl-yoneda-Id ≐ refl.
```

The proof that it is a retraction requires the
[function extensionality axiom](foundation.function-extensionality.md). However,
function extensionality will become indispensable regardless when we proceed to
proving miscellaneous algebraic laws of the judgmentally compositional identity
type.

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  yoneda-eq-eq : x ＝ y → x ＝ʸ y
  yoneda-eq-eq p z q = q ∙ᵣ p

  eq-yoneda-eq : x ＝ʸ y → x ＝ y
  eq-yoneda-eq f = f x refl

  is-section-eq-yoneda-eq :
    is-section yoneda-eq-eq eq-yoneda-eq
  is-section-eq-yoneda-eq f =
    eq-multivariable-htpy 2
      ( λ _ p → inv (commutative-postconcatr-refl-Id-yoneda-Id f p))

  is-retraction-eq-yoneda-eq :
    is-retraction yoneda-eq-eq eq-yoneda-eq
  is-retraction-eq-yoneda-eq p = left-unit-concatr

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

The reflexivity elements are mapped to reflexivity elements judgmentally.

```agda
module _
  {l : Level} {A : UU l}
  where

  is-section-eq-yoneda-eq-refl :
    {x : A} → yoneda-eq-eq (eq-yoneda-eq (refl-yoneda-Id {x = x})) ＝ refl-yoneda-Id
  is-section-eq-yoneda-eq-refl = refl

  preserves-refl-yoneda-eq-eq :
    {x : A} → yoneda-eq-eq (refl {x = x}) ＝ refl-yoneda-Id
  preserves-refl-yoneda-eq-eq = refl

  preserves-refl-eq-yoneda-eq :
    {x : A} → eq-yoneda-eq (refl-yoneda-Id {x = x}) ＝ refl
  preserves-refl-eq-yoneda-eq = refl
```

An alternative definition of `yoneda-eq-eq'` using the judgmentally left unital
concatenation operation on standard identity types.

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
      ( λ _ p → inv (commutative-postconcat-refl-Id-yoneda-Id f p))

  is-retraction-eq-yoneda-eq' :
    is-retraction yoneda-eq-eq' eq-yoneda-eq
  is-retraction-eq-yoneda-eq' p = refl

module _
  {l : Level} {A : UU l}
  where

  preserves-refl-yoneda-eq-eq' :
    {x : A} → yoneda-eq-eq' (refl {x = x}) ＝ refl-yoneda-Id
  preserves-refl-yoneda-eq-eq' =
    eq-multivariable-htpy 2 (λ _ p → right-unit)
```

### The induction principle for judgmentally compositional identity types

The judgmentally compositional identity types satisfy the induction principle of
the identity types. This states that given a base point `x : A` and a family of
types over the identity types based at `x`, `B : (y : A) (f : x ＝ʸ y) → UU l2`,
then to construct a dependent function `f : (y : A) (f : x ＝ʸ y) → B y p` it
suffices to define it at `f x refl-yoneda-Id`.

**Note.** A drawback of the judgmentally compositional identity types is that
they do not satisfy a judgmental computation rule for this induction principle.

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

  dependent-universal-property-identity-system-yoneda-Id :
    dependent-universal-property-identity-system
      ( yoneda-Id x)
      ( refl-yoneda-Id)
  dependent-universal-property-identity-system-yoneda-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( refl-yoneda-Id)
      ( is-torsorial-yoneda-Id)

module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (f : x ＝ʸ y) → UU l2)
  where

  ind-yoneda-Id :
    (b : B x refl-yoneda-Id) {y : A} (f : x ＝ʸ y) → B y f
  ind-yoneda-Id b {y} =
    map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)
      ( b)
      ( y)

  compute-ind-yoneda-Id :
    (b : B x refl-yoneda-Id) →
    ind-yoneda-Id b refl-yoneda-Id ＝ b
  compute-ind-yoneda-Id =
    is-section-map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)

  uniqueness-ind-yoneda-Id :
    (b : (y : A) (f : x ＝ʸ y) → B y f) →
    (λ y → ind-yoneda-Id (b x refl-yoneda-Id) {y}) ＝ b
  uniqueness-ind-yoneda-Id =
    is-retraction-map-inv-is-equiv
      ( dependent-universal-property-identity-system-yoneda-Id B)

module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (f : x ＝ʸ y) → UU l2)
  where

  ind-yoneda-Id' :
    (b : B x refl-yoneda-Id) {y : A} (f : x ＝ʸ y) → B y (yoneda-eq-eq (f x refl))
  ind-yoneda-Id' b {y} f = ind-Id x (λ y p → B y (yoneda-eq-eq p)) b y (f x refl)

  -- compute-ind-yoneda-Id :
  --   (b : B x refl-yoneda-Id) →
  --   ind-yoneda-Id b refl-yoneda-Id ＝ b
  -- compute-ind-yoneda-Id =
  --   is-section-map-inv-is-equiv
  --     ( dependent-universal-property-identity-system-yoneda-Id B)
```

While the induction principle does not have the ideal reduction behaviour, the
non-dependent eliminator does:

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  {B : A → UU l2}
  where

  rec-yoneda-Id :
    (b : B x) {y : A} → x ＝ʸ y → B y
  rec-yoneda-Id b {y} p = tr B (p x refl) b

  compute-rec-yoneda-Id :
    (b : B x) → rec-yoneda-Id b refl-yoneda-Id ＝ b
  compute-rec-yoneda-Id b = refl

  uniqueness-rec-yoneda-Id :
    (b : (y : A) → x ＝ʸ y → B y) →
    (λ y → rec-yoneda-Id (b x refl-yoneda-Id) {y}) ＝ b
  uniqueness-rec-yoneda-Id b =
    ( inv
      ( uniqueness-ind-yoneda-Id
        ( λ y _ → B y)
        ( λ y → rec-yoneda-Id (b x refl-yoneda-Id)))) ∙
    ( uniqueness-ind-yoneda-Id (λ y _ → B y) b)
```

## Structure

The judgmentally compositional identity types form a judgmentally compositional
weak groupoidal structure on types.

### Inverting judgmentally compositional identifications

We consider two ways of defining the inversion operation on judgmentally
compositional identifications: by the judgmentally left unital, and judgmentally
right unital concatenation operation on the underlying identity type
respectively. The latter enjoys the computational property

```text
  inv refl ≐ refl,
```

hence will be preferred elsewhere.

#### The inversion operation defined by the judgmentally left unital concatenation operation on identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  invl-yoneda-Id : {x y : A} → x ＝ʸ y → y ＝ʸ x
  invl-yoneda-Id {x} f z p = p ∙ inv (f x refl)

  compute-invl-yoneda-Id-refl :
    {x : A} →
    invl-yoneda-Id (refl-yoneda-Id {x = x}) ＝ refl-yoneda-Id
  compute-invl-yoneda-Id-refl = eq-multivariable-htpy 2 (λ _ p → right-unit)

  invl-invl-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) → invl-yoneda-Id (invl-yoneda-Id f) ＝ f
  invl-invl-yoneda-Id {x} f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ap (p ∙_) (inv-inv (f x refl)) ∙
        inv (commutative-postconcat-refl-Id-yoneda-Id f p))
```

The inversion operation corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-invl-yoneda-eq-eq :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ invl-yoneda-Id (yoneda-eq-eq p)
  preserves-invl-yoneda-eq-eq p =
    eq-multivariable-htpy 2
      ( λ _ q →
        ( eq-concat-concatr q (inv p)) ∙
        ( ap (λ r → q ∙ inv r) (inv left-unit-concatr)))

  preserves-invl-eq-yoneda-eq :
    {x y : A} (f : x ＝ʸ y) →
    eq-yoneda-eq (invl-yoneda-Id f) ＝ inv (eq-yoneda-eq f)
  preserves-invl-eq-yoneda-eq f = refl
```

#### The inversion operation defined by the judgmentally right unital concatenation operation on identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  invr-yoneda-Id : {x y : A} → x ＝ʸ y → y ＝ʸ x
  invr-yoneda-Id {x} f z p = p ∙ᵣ inv (f x refl)

  compute-invr-yoneda-Id-refl :
    {x : A} →
    invr-yoneda-Id (refl-yoneda-Id {x = x}) ＝ refl-yoneda-Id
  compute-invr-yoneda-Id-refl = refl

  invr-invr-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) →
    invr-yoneda-Id (invr-yoneda-Id f) ＝ f
  invr-invr-yoneda-Id {x} f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap (p ∙ᵣ_) (ap inv left-unit-concatr ∙ inv-inv (f x refl))) ∙
        ( inv (commutative-postconcatr-refl-Id-yoneda-Id f p)))
```

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-invr-yoneda-eq-eq' :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ invr-yoneda-Id (yoneda-eq-eq' p)
  preserves-invr-yoneda-eq-eq' p = refl

  preserves-invr-yoneda-eq-eq :
    {x y : A} (p : x ＝ y) →
    yoneda-eq-eq (inv p) ＝ invr-yoneda-Id (yoneda-eq-eq p)
  preserves-invr-yoneda-eq-eq refl = refl

  preserves-invr-eq-yoneda-eq :
    {x y : A} (f : x ＝ʸ y) →
    eq-yoneda-eq (invr-yoneda-Id f) ＝ inv (eq-yoneda-eq f)
  preserves-invr-eq-yoneda-eq {x} {y} f = left-unit-concatr
```

We will prefer the inversion operation defined by the judgmentally right unital
concatenation operation on identifications by convention, as it satisfies the
judgmental computation law

```text
  inv refl ≐ refl.
```

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-yoneda-Id : {x y : A} → x ＝ʸ y → y ＝ʸ x
  inv-yoneda-Id = invr-yoneda-Id

  compute-inv-yoneda-Id-refl :
    {x : A} → inv-yoneda-Id (refl-yoneda-Id {x = x}) ＝ refl-yoneda-Id
  compute-inv-yoneda-Id-refl = compute-invr-yoneda-Id-refl

  inv-inv-yoneda-Id :
    {x y : A} (f : x ＝ʸ y) → inv-yoneda-Id (inv-yoneda-Id f) ＝ f
  inv-inv-yoneda-Id = invr-invr-yoneda-Id
```

### Concatenation of judgmentally compositional identifications

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
    commutative-postconcat-refl-Id-yoneda-Id g (f x refl)
```

### The groupoidal laws for the judgmentally compositional identity types

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  assoc-yoneda-Id :
    (f : x ＝ʸ y) {z w : A} (g : y ＝ʸ z) (h : z ＝ʸ w) →
    (f ∙ʸ g) ∙ʸ h ＝ f ∙ʸ (g ∙ʸ h)
  assoc-yoneda-Id f g h = refl

  left-unit-yoneda-Id :
    {f : x ＝ʸ y} → refl-yoneda-Id ∙ʸ f ＝ f
  left-unit-yoneda-Id = refl

  right-unit-yoneda-Id :
    {f : x ＝ʸ y} → f ∙ʸ refl-yoneda-Id ＝ f
  right-unit-yoneda-Id = refl

  left-inv-yoneda-Id :
    (f : x ＝ʸ y) → inv-yoneda-Id f ∙ʸ f ＝ refl-yoneda-Id
  left-inv-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( commutative-postconcatr-Id-yoneda-Id f p (inv (f x refl))) ∙
        ( ap (p ∙ᵣ_) (compute-inv-Id-yoneda-Id f)))

  left-invl-yoneda-Id :
    (f : x ＝ʸ y) → invl-yoneda-Id f ∙ʸ f ＝ refl-yoneda-Id
  left-invl-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( commutative-postconcat-Id-yoneda-Id f p (inv (f x refl))) ∙
        ( ap (p ∙_) (compute-inv-Id-yoneda-Id f) ∙ right-unit))

  right-inv-yoneda-Id :
    (f : x ＝ʸ y) → f ∙ʸ inv-yoneda-Id f ＝ refl-yoneda-Id
  right-inv-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( _∙ᵣ inv (f x refl))
          ( commutative-postconcatr-refl-Id-yoneda-Id f p)) ∙
        ( assoc-concatr p (f x refl) (inv (f x refl))) ∙
        ( ap (p ∙ᵣ_) (right-inv-concatr (f x refl))))

  right-invl-yoneda-Id :
    (f : x ＝ʸ y) → f ∙ʸ invl-yoneda-Id f ＝ refl-yoneda-Id
  right-invl-yoneda-Id f =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( _∙ inv (f x refl))
          ( commutative-postconcat-refl-Id-yoneda-Id f p)) ∙
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
              ( commutative-postconcatr-refl-Id-yoneda-Id g (f x refl))) ∙
            ( distributive-inv-concatr (f x refl) (g y refl)))) ∙
          ( inv (assoc-concatr p (inv (g y refl)) (inv (f x refl)))))

  distributive-invl-concat-yoneda-Id :
    (f : x ＝ʸ y) {z : A} (g : y ＝ʸ z) →
    invl-yoneda-Id (f ∙ʸ g) ＝ invl-yoneda-Id g ∙ʸ invl-yoneda-Id f
  distributive-invl-concat-yoneda-Id f g =
    eq-multivariable-htpy 2
      ( λ _ p →
        ( ap
          ( p ∙_)
          ( ( ap
              ( inv)
              ( commutative-postconcat-refl-Id-yoneda-Id g (f x refl))) ∙
            ( distributive-inv-concat (f x refl) (g y refl)))) ∙
        ( inv (assoc p (inv (g y refl)) (inv (f x refl)))))
```

### Action of functions on judgmentally compositional identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A} (f : A → B)
  where

  ap-yoneda-Id : x ＝ʸ y → f x ＝ʸ f y
  ap-yoneda-Id p .(f x) refl = ap f (p x refl)
```

### Transport along judgmentally compositional identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  where

  tr-yoneda-Id : x ＝ʸ y → B x → B y
  tr-yoneda-Id p = tr B (p x refl)
```

### `htpy-compositional-eq`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  htpy-yoneda-eq : f ＝ʸ g → f ~ g
  htpy-yoneda-eq p = htpy-eq (p f refl)
```

### `equiv-compositional-eq`

```agda
module _
  {l1 : Level} {A B : UU l1}
  where

  equiv-yoneda-eq : A ＝ʸ B → A ≃ B
  equiv-yoneda-eq p = equiv-eq (p A refl)
```

## See also

- [The judgmentally involutive identity types](foundation.judgmentally-involutive-identity-types.md)
  for an identity relation that is strictly involutive, one-sided unital, and
  has a judgmentally computational induction principle.
- [The computational identity types](foundation.computational-identity-types.md)
  for an identity relation that is judgmentally involutive, associative, and
  one-sided unital, but does not have a judgmentally computational induction
  principle.

## References

- <https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ>
