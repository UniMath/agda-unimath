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
standard identity types, but satisfies the judgmental law

```text
  inv (inv p) ＝ p.
```

In addition, we maintain the following judgmental laws

- `inv refl ＝ refl`
- `ind-Id f refl ＝ f refl`
- `refl ∙ p ＝ p`

among other more technical ones considered in this file.

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

We define the concatenation operation on the judgmentally involutive
identifications using the
[judgmentally right unital concatenation operation on identifications](foundation.judgmentally-right-unital-concatenation-identifications.md),
to obtain a one-sided judgmental unit law. There is both a judgmentally left
unital definition and a judgmentally right unital definition. To be consistent
with the convention for the standard identity types, we take the judgmentally
left unital concatenation operation as the default.

#### The judgmentally left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ⁱ_
  _∙ⁱ_ : {x y z : A} → x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
  (w , p , q) ∙ⁱ (w' , p' , q') = (w' , p' , (q' ∙ᵣ inv p) ∙ᵣ q)

  concat-involutive-Id : {x y : A} → x ＝ⁱ y → (z : A) → y ＝ⁱ z → x ＝ⁱ z
  concat-involutive-Id p z q = p ∙ⁱ q

  concat-involutive-Id' : (x : A) {y z : A} → y ＝ⁱ z → x ＝ⁱ y → x ＝ⁱ z
  concat-involutive-Id' x q p = p ∙ⁱ q

  commutative-concat-involutive-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    involutive-eq-eq (p ∙ q) ＝ involutive-eq-eq p ∙ⁱ involutive-eq-eq q
  commutative-concat-involutive-eq-eq refl q = refl

  commutative-concat-eq-involutive-eq :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) →
    eq-involutive-eq (p ∙ⁱ q) ＝ eq-involutive-eq p ∙ eq-involutive-eq q
  commutative-concat-eq-involutive-eq (w , p , q) (w' , p' , q') =
    ( ap
      ( _∙ p')
      ( ( distributive-inv-concatr (q' ∙ᵣ inv p) q) ∙
        ( ( ap
            ( inv q ∙ᵣ_)
            ( ( distributive-inv-concatr q' (inv p)) ∙
              ( ap (_∙ᵣ inv q') (inv-inv p)))) ∙
          ( inv (assoc-concatr (inv q) p (inv q'))) ∙
          ( eq-double-concat-concatr-left-associated (inv q) p (inv q'))))) ∙
    ( assoc (inv q ∙ p) (inv q') p')
```

#### The judgmentally right unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ᵣⁱ_
  _∙ᵣⁱ_ : {x y z : A} → x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
  (w , p , q) ∙ᵣⁱ (w' , p' , q') = (w , (p ∙ᵣ inv q') ∙ᵣ p' , q)

  concatr-involutive-Id : {x y : A} → x ＝ⁱ y → (z : A) → y ＝ⁱ z → x ＝ⁱ z
  concatr-involutive-Id p z q = p ∙ᵣⁱ q

  concatr-involutive-Id' : (x : A) {y z : A} → y ＝ⁱ z → x ＝ⁱ y → x ＝ⁱ z
  concatr-involutive-Id' x q p = p ∙ᵣⁱ q

  eq-concat-concatr-involutive-Id :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) → p ∙ᵣⁱ q ＝ p ∙ⁱ q
  eq-concat-concatr-involutive-Id (w , refl , q) (w' , p' , refl) =
    eq-pair-eq-pr2 (eq-pair (left-unit-concatr) (inv left-unit-concatr))

  commutative-concatr-involutive-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    involutive-eq-eq (p ∙ q) ＝ involutive-eq-eq p ∙ᵣⁱ involutive-eq-eq q
  commutative-concatr-involutive-eq-eq p refl = ap involutive-eq-eq right-unit

  commutative-concatr-eq-involutive-eq :
    {x y z : A} (p : x ＝ⁱ y) (q : y ＝ⁱ z) →
    eq-involutive-eq (p ∙ᵣⁱ q) ＝ eq-involutive-eq p ∙ eq-involutive-eq q
  commutative-concatr-eq-involutive-eq (w , p , q) (w' , p' , q') =
    ( ap
      ( inv q ∙_)
      ( ( eq-double-concat-concatr-left-associated p (inv q') p') ∙
        ( assoc p (inv q') p'))) ∙
    ( inv (assoc (inv q) p (inv q' ∙ p')))
```

### The groupoidal laws for the judgmentally involutive identity types

The general proof-technique is to induct on the necessary paths to make the left
endpoints judgmentally equal, and then proceed by reasoning with the
groupoid-laws of the underlying identity system.

#### The groupoidal laws for the judgmentally left unital concatenation operation

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  assoc-involutive-Id :
    (p : x ＝ⁱ y) (q : y ＝ⁱ z) (r : z ＝ⁱ w) →
    ((p ∙ⁱ q) ∙ⁱ r) ＝ (p ∙ⁱ (q ∙ⁱ r))
  assoc-involutive-Id (_ , p , q) (_ , p' , q') (_ , p'' , q'') =
    eq-pair-eq-pr2
      ( eq-pair-eq-pr2
        ( ( inv (assoc-concatr (q'' ∙ᵣ inv p') (q' ∙ᵣ inv p) q)) ∙
          ( ap (_∙ᵣ q) (inv (assoc-concatr (q'' ∙ᵣ inv p') q' (inv p))))))

module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-involutive-Id :
    {p : x ＝ⁱ y} → refl-involutive-Id ∙ⁱ p ＝ p
  left-unit-involutive-Id = refl

  right-unit-involutive-Id :
    {p : x ＝ⁱ y} → p ∙ⁱ refl-involutive-Id ＝ p
  right-unit-involutive-Id {p = .y , refl , q} =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 left-unit-concatr)

  left-inv-involutive-Id :
    (p : x ＝ⁱ y) → inv-involutive-Id p ∙ⁱ p ＝ refl-involutive-Id
  left-inv-involutive-Id (.y , refl , q) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-concatr q))

  right-inv-involutive-Id :
    (p : x ＝ⁱ y) → p ∙ⁱ inv-involutive-Id p ＝ refl-involutive-Id
  right-inv-involutive-Id (.x , p , refl) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-concatr p))

  distributive-inv-concat-involutive-Id :
    (p : x ＝ⁱ y) {z : A} (q : y ＝ⁱ z) →
    inv-involutive-Id (p ∙ⁱ q) ＝ inv-involutive-Id q ∙ⁱ inv-involutive-Id p
  distributive-inv-concat-involutive-Id (.y , refl , q') (.y , p' , refl) =
    eq-pair-eq-pr2 (eq-pair (left-unit-concatr) (inv left-unit-concatr))
```

#### The groupoidal laws for the judgmentally right unital concatenation operation

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  assoc-concatr-involutive-Id :
    (p : x ＝ⁱ y) (q : y ＝ⁱ z) (r : z ＝ⁱ w) →
    ((p ∙ᵣⁱ q) ∙ᵣⁱ r) ＝ (p ∙ᵣⁱ (q ∙ᵣⁱ r))
  assoc-concatr-involutive-Id (_ , p , q) (_ , p' , q') (_ , p'' , q'') =
    eq-pair-eq-pr2
      ( eq-pair
        ( ( assoc-concatr (p ∙ᵣ inv q' ∙ᵣ p') (inv q'') p'') ∙
          ( assoc-concatr (p ∙ᵣ inv q') p' (inv q'' ∙ᵣ p'')) ∙
          ( ap (p ∙ᵣ inv q' ∙ᵣ_) (inv (assoc-concatr p' (inv q'') p''))))
        ( refl))

module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-concatr-involutive-Id :
    {p : x ＝ⁱ y} → refl-involutive-Id ∙ᵣⁱ p ＝ p
  left-unit-concatr-involutive-Id {p = .x , p , refl} =
    eq-pair-eq-pr2 (eq-pair left-unit-concatr refl)

  right-unit-concatr-involutive-Id :
    {p : x ＝ⁱ y} → p ∙ᵣⁱ refl-involutive-Id ＝ p
  right-unit-concatr-involutive-Id = refl

  left-inv-concatr-involutive-Id :
    (p : x ＝ⁱ y) → inv-involutive-Id p ∙ᵣⁱ p ＝ refl-involutive-Id
  left-inv-concatr-involutive-Id (.y , refl , q) =
    eq-pair-eq-pr2 (eq-pair (right-inv-concatr q) refl)

  right-inv-concatr-involutive-Id :
    (p : x ＝ⁱ y) → p ∙ᵣⁱ inv-involutive-Id p ＝ refl-involutive-Id
  right-inv-concatr-involutive-Id (.x , p , refl) =
    eq-pair-eq-pr2 (eq-pair (right-inv-concatr p) refl)

  distributive-inv-concatr-involutive-Id :
    (p : x ＝ⁱ y) {z : A} (q : y ＝ⁱ z) →
    inv-involutive-Id (p ∙ᵣⁱ q) ＝ inv-involutive-Id q ∙ᵣⁱ inv-involutive-Id p
  distributive-inv-concatr-involutive-Id (.y , refl , q) (.y , p' , refl) =
    eq-pair-eq-pr2 (eq-pair (inv left-unit-concatr) (left-unit-concatr))
```

## References

- <https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ>