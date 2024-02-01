# Judgmentally involutive identity types

```agda
module foundation.judgmentally-involutive-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
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
{{#concept "judgmentally involutive identity types" Agda=involutive-Id}}

```text
  (x ＝ⁱ y) := Σ (z : A) ((z ＝ y) × (z ＝ x))
```

This type family is [equivalent](foundation-core.equivalences.md) to the
standard identity types, but satisfies the law

```text
  inv (inv p) ＝ p
```

judgmentally.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  involutive-Id : (x y : A) → UU l
  involutive-Id x y = Σ A (λ z → (z ＝ y) × (z ＝ x))

  infix 6 _＝ⁱ_
  _＝ⁱ_ : A → A → UU l
  (a ＝ⁱ b) = involutive-Id a b

  refl-involutive-Id : {x : A} → x ＝ⁱ x
  refl-involutive-Id {x} = (x , refl , refl)
```

## Properties

### The judgmentally involutive identity types are equivalent to the standard identity types

In fact, the [retraction](foundation-core.retractions.md) is judgmental, and the
equivalence preserves the groupoid structure.

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  involutive-eq-eq : x ＝ y → x ＝ⁱ y
  involutive-eq-eq p = (x , p , refl)

  eq-involutive-eq : x ＝ⁱ y → x ＝ y
  eq-involutive-eq (z , p , q) = inv q ∙ p

  is-section-eq-involutive-eq : is-section involutive-eq-eq eq-involutive-eq
  is-section-eq-involutive-eq (z , p , refl) = refl

  is-retraction-eq-involutive-eq :
    is-retraction involutive-eq-eq eq-involutive-eq
  is-retraction-eq-involutive-eq p = refl

  is-equiv-involutive-eq-eq : is-equiv involutive-eq-eq
  pr1 (pr1 is-equiv-involutive-eq-eq) = eq-involutive-eq
  pr2 (pr1 is-equiv-involutive-eq-eq) = is-section-eq-involutive-eq
  pr1 (pr2 is-equiv-involutive-eq-eq) = eq-involutive-eq
  pr2 (pr2 is-equiv-involutive-eq-eq) = is-retraction-eq-involutive-eq

  is-equiv-eq-involutive-eq : is-equiv eq-involutive-eq
  pr1 (pr1 is-equiv-eq-involutive-eq) = involutive-eq-eq
  pr2 (pr1 is-equiv-eq-involutive-eq) = is-retraction-eq-involutive-eq
  pr1 (pr2 is-equiv-eq-involutive-eq) = involutive-eq-eq
  pr2 (pr2 is-equiv-eq-involutive-eq) = is-section-eq-involutive-eq

  equiv-involutive-eq-eq : (x ＝ y) ≃ (x ＝ⁱ y)
  pr1 equiv-involutive-eq-eq = involutive-eq-eq
  pr2 equiv-involutive-eq-eq = is-equiv-involutive-eq-eq

  equiv-eq-involutive-eq : (x ＝ⁱ y) ≃ (x ＝ y)
  pr1 equiv-eq-involutive-eq = eq-involutive-eq
  pr2 equiv-eq-involutive-eq = is-equiv-eq-involutive-eq

module _
  {l : Level} {A : UU l}
  where

  involutive-eq-eq-refl :
    {x : A} → involutive-eq-eq (refl {x = x}) ＝ refl-involutive-Id
  involutive-eq-eq-refl = refl

  eq-involutive-eq-refl :
    {x : A} → eq-involutive-eq (refl-involutive-Id {x = x}) ＝ refl
  eq-involutive-eq-refl = refl
```

### The induction principle for judgmentally involutive identity types

The judgementally involutive identity types satisfy the induction principle of
the identity types. This states that given a base point `x : A` and a family of
types over the identity types based at `x`, `B : (y : A) (p : x ＝ⁱ y) → UU l2`,
then to construct a dependent function `f : (y : A) (p : x ＝ⁱ y) → B y p` it
suffices to define it at `f x refl-involutive-Id`.

**Note.** The only reason we must apply
[function extensionality](foundation.function-extensionality.md) is to show
uniqueness of the induction principle up to _equality_.

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-involutive-Id : is-torsorial (involutive-Id x)
  is-torsorial-involutive-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-involutive-eq {x = x} {y}))
      ( is-torsorial-Id x)

  dependent-universal-property-identity-system-involutive-Id :
    dependent-universal-property-identity-system
      ( involutive-Id x)
      ( refl-involutive-Id)
  dependent-universal-property-identity-system-involutive-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( refl-involutive-Id)
      ( is-torsorial-involutive-Id)

module _
  {l1 l2 : Level} {A : UU l1}
  (x : A) (B : (y : A) (p : x ＝ⁱ y) → UU l2)
  where

  ind-involutive-Id :
    B x refl-involutive-Id → (y : A) (p : x ＝ⁱ y) → B y p
  ind-involutive-Id b .x (.x , refl , refl) = b

  compute-ind-involutive-Id :
    (b : B x refl-involutive-Id) → ind-involutive-Id b x refl-involutive-Id ＝ b
  compute-ind-involutive-Id b = refl

  uniqueness-ind-involutive-Id :
    (f : (y : A) (p : x ＝ⁱ y) → B y p) →
    ind-involutive-Id (f x refl-involutive-Id) ＝ f
  uniqueness-ind-involutive-Id f =
    eq-multivariable-htpy 2 (λ where .x (.x , refl , refl) → refl)
```

## Structure

The judgementally involutive identity types form a judgmentally involutive weak
groupoidal structure on types.

### Inverting judgmentally involutive identifications

We have an inversion operation on `involutive-Id` that satisfies the judgmental
laws

```text
  inv (inv p) ＝ p
```

and

```text
  inv refl ＝ refl.
```

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-involutive-Id : {x y : A} → x ＝ⁱ y → y ＝ⁱ x
  inv-involutive-Id (z , p , q) = (z , q , p)

  compute-inv-involutive-Id-refl :
    {x : A} →
    inv-involutive-Id (refl-involutive-Id {x = x}) ＝ refl-involutive-Id
  compute-inv-involutive-Id-refl = refl

  inv-inv-involutive-Id :
    {x y : A} (p : x ＝ⁱ y) → inv-involutive-Id (inv-involutive-Id p) ＝ p
  inv-inv-involutive-Id p = refl
```

The inversion operation corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-inv-involutive-eq-eq :
    {x y : A} (p : x ＝ y) →
    involutive-eq-eq (inv p) ＝ inv-involutive-Id (involutive-eq-eq p)
  commutative-inv-involutive-eq-eq refl = refl

  commutative-inv-eq-involutive-eq :
    {x y : A} (p : x ＝ⁱ y) →
    eq-involutive-eq (inv-involutive-Id p) ＝ inv (eq-involutive-eq p)
  commutative-inv-eq-involutive-eq (z , p , q) =
    ap (inv p ∙_) (inv (inv-inv q)) ∙ inv (distributive-inv-concat (inv q) p)
```

### Concatenation of judgmentally involutive identifications

**Note.** We define the concatenation operation on the judgmentally involutive
identifications using the
[judgmentally right unital concatenation operation on identifications](foundation.judgmentally-right-unital-concatenation-operation-identifications.md),
to obtain a judgmental _left_ unit law.

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ⁱ_
  _∙ⁱ_ : {x y z : A} → x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
  (z , p , q) ∙ⁱ (z' , p' , q') = (z' , p' , (q' ∙ᵣ inv p) ∙ᵣ q)

  concat-involutive-Id : {x y : A} → x ＝ⁱ y → (z : A) → y ＝ⁱ z → x ＝ⁱ z
  concat-involutive-Id p z q = p ∙ⁱ q

  concat-involutive-Id' : (x : A) {y z : A} → y ＝ⁱ z → x ＝ⁱ y → x ＝ⁱ z
  concat-involutive-Id' x q p = p ∙ⁱ q
```

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ₗⁱ_
  _∙ₗⁱ_ : {x y z : A} → x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
  (z , p , q) ∙ₗⁱ (z' , p' , q') = (z' , p' , (q' ∙ inv p) ∙ q)

  lconcat-involutive-Id : {x y : A} → x ＝ⁱ y → (z : A) → y ＝ⁱ z → x ＝ⁱ z
  lconcat-involutive-Id p z q = p ∙ₗⁱ q

  lconcat-involutive-Id' : (x : A) {y z : A} → y ＝ⁱ z → x ＝ⁱ y → x ＝ⁱ z
  lconcat-involutive-Id' x q p = p ∙ₗⁱ q

  eq-concat-lconcat-involutive-Id :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) → p ∙ₗⁱ q ＝ p ∙ⁱ q
  eq-concat-lconcat-involutive-Id (z , p , q) (z' , p' , q') =
    eq-pair-eq-pr2
      ( eq-pair-eq-pr2
        ( eq-double-rconcat-concat-left-associated q' (inv p) q))
```

The concatenation operation corresponds to the standard concatenation operation
on identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  commutative-concat-involutive-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    involutive-eq-eq (p ∙ q) ＝ involutive-eq-eq p ∙ⁱ involutive-eq-eq q
  commutative-concat-involutive-eq-eq refl q = refl

  commutative-lconcat-eq-involutive-eq :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) →
    eq-involutive-eq (p ∙ₗⁱ q) ＝ eq-involutive-eq p ∙ eq-involutive-eq q
  commutative-lconcat-eq-involutive-eq (z , p , q) (z' , p' , q') =
    ( ap
      ( _∙ p')
      ( ( distributive-inv-concat (q' ∙ inv p) q) ∙
        ( ap
          ( inv q ∙_)
          ( distributive-inv-concat q' (inv p) ∙ ap (_∙ inv q') (inv-inv p))) ∙
        ( inv (assoc (inv q) p (inv q'))))) ∙
    ( assoc (inv q ∙ p) (inv q') p')

  commutative-concat-eq-involutive-eq :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) →
    eq-involutive-eq (p ∙ⁱ q) ＝ eq-involutive-eq p ∙ eq-involutive-eq q
  commutative-concat-eq-involutive-eq (z , p , q) (z' , p' , q') =
    ( ap
      ( λ x → inv x ∙ p')
      ( eq-double-concat-rconcat-left-associated q' (inv p) q)) ∙
    ( commutative-lconcat-eq-involutive-eq (z , p , q) (z' , p' , q'))
```

### The groupoidal laws for the judgmentally involutive identity types

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc-involutive-Id :
    {x y z w : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) (r : z ＝ⁱ w) →
    ((p ∙ⁱ q) ∙ⁱ r) ＝ (p ∙ⁱ (q ∙ⁱ r))
  assoc-involutive-Id (z , p , q) (z' , p' , q') (z'' , p'' , q'') =
    eq-pair-eq-pr2
      ( eq-pair-eq-pr2
        ( ( inv (assoc-rconcat (q'' ∙ᵣ inv p') (q' ∙ᵣ inv p) q)) ∙
          ( ap (_∙ᵣ q) (inv (assoc-rconcat (q'' ∙ᵣ inv p') q' (inv p))))))

  left-unit-involutive-Id :
    {x y : A} {p : x ＝ⁱ y} → refl-involutive-Id ∙ⁱ p ＝ p
  left-unit-involutive-Id = refl

  right-unit-involutive-Id :
    {x y : A} {p : x ＝ⁱ y} → p ∙ⁱ refl-involutive-Id ＝ p
  right-unit-involutive-Id {p = z , refl , q} =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 left-unit-rconcat)

  left-inv-involutive-Id :
    {x y : A} (p : x ＝ⁱ y) → inv-involutive-Id p ∙ⁱ p ＝ refl-involutive-Id
  left-inv-involutive-Id (z , refl , q) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-rconcat q))

  right-inv-involutive-Id :
    {x y : A} (p : x ＝ⁱ y) → p ∙ⁱ inv-involutive-Id p ＝ refl-involutive-Id
  right-inv-involutive-Id (z , p , refl) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-rconcat p))

  distributive-inv-concat-involutive-Id :
    {x y : A} (p : x ＝ⁱ y) {z : A} (q : y ＝ⁱ z) →
    inv-involutive-Id (p ∙ⁱ q) ＝ inv-involutive-Id q ∙ⁱ inv-involutive-Id p
  distributive-inv-concat-involutive-Id (z , refl , refl) (z' , p' , refl) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (inv left-unit-rconcat))
```

## References

- <https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ>
