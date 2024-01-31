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
  (x ＝⁻ y) := Σ (z : A) ((z ＝ y) × (z ＝ x))
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

  infix 6 _＝⁻_
  _＝⁻_ : A → A → UU l
  (a ＝⁻ b) = involutive-Id a b

  refl-involutive-Id : {x : A} → x ＝⁻ x
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

  involutive-eq-eq : x ＝ y → x ＝⁻ y
  involutive-eq-eq p = (x , p , refl)

  eq-involutive-eq : x ＝⁻ y → x ＝ y
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

  equiv-involutive-eq-eq : (x ＝ y) ≃ (x ＝⁻ y)
  pr1 equiv-involutive-eq-eq = involutive-eq-eq
  pr2 equiv-involutive-eq-eq = is-equiv-involutive-eq-eq

  equiv-eq-involutive-eq : (x ＝⁻ y) ≃ (x ＝ y)
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
types over the identity types based at `x`, `B : (y : A) (p : x ＝⁻ y) → UU l2`,
then to construct a dependent function `f : (y : A) (p : x ＝⁻ y) → B y p` it
suffices to define it at `f x refl-involutive-Id`.

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-involutive-Id : is-torsorial (involutive-Id x)
  is-torsorial-involutive-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-involutive-eq {x = x} {y}))
      ( is-torsorial-path x)

  dependent-universal-property-identity-system-involutive-Id :
    dependent-universal-property-identity-system
      ( involutive-Id x)
      ( refl-involutive-Id)
  dependent-universal-property-identity-system-involutive-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( refl-involutive-Id)
      ( is-torsorial-involutive-Id)

  ind-involutive-Id :
    {l1 l2 : Level} {A : UU l1}
    (x : A) (B : (y : A) (p : x ＝⁻ y) → UU l2) →
    (B x refl-involutive-Id) → (y : A) (p : x ＝⁻ y) → B y p
  ind-involutive-Id x B b .x (.x , refl , refl) = b
```

## Structure

The judgementally involutive identity types form a judgmentally involutive weak
groupoidal structure on types.

### Inverting judgmentally involutive identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-involutive-eq : {x y : A} → x ＝⁻ y → y ＝⁻ x
  inv-involutive-eq (z , p , q) = (z , q , p)

  inv-inv-involutive-eq :
    {x y : A} (p : x ＝⁻ y) → inv-involutive-eq (inv-involutive-eq p) ＝ p
  inv-inv-involutive-eq p = refl
```

The inversion operation corresponds to the standard inversion operation on
identifications:

```agda
module _
  {l : Level} {A : UU l}
  where

  distributive-inv-involutive-eq-eq :
    {x y : A} (p : x ＝ y) →
    involutive-eq-eq (inv p) ＝ inv-involutive-eq (involutive-eq-eq p)
  distributive-inv-involutive-eq-eq refl = refl

  distributive-inv-eq-involutive-eq :
    {x y : A} (p : x ＝⁻ y) →
    eq-involutive-eq (inv-involutive-eq p) ＝ inv (eq-involutive-eq p)
  distributive-inv-eq-involutive-eq (z , p , q) =
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

  infixl 15 _∙⁻_
  _∙⁻_ : {x y z : A} → x ＝⁻ y → y ＝⁻ z → x ＝⁻ z
  (z , p , q) ∙⁻ (z' , p' , q') = (z' , p' , (q' ∙ᵣ inv p) ∙ᵣ q)

  concat-involutive-eq : {x y : A} → x ＝⁻ y → (z : A) → y ＝⁻ z → x ＝⁻ z
  concat-involutive-eq p z q = p ∙⁻ q

  concat-involutive-eq' : (x : A) {y z : A} → y ＝⁻ z → x ＝⁻ y → x ＝⁻ z
  concat-involutive-eq' x q p = p ∙⁻ q
```

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ₗ⁻_
  _∙ₗ⁻_ : {x y z : A} → x ＝⁻ y → y ＝⁻ z → x ＝⁻ z
  (z , p , q) ∙ₗ⁻ (z' , p' , q') = (z' , p' , (q' ∙ inv p) ∙ q)

  lconcat-involutive-eq : {x y : A} → x ＝⁻ y → (z : A) → y ＝⁻ z → x ＝⁻ z
  lconcat-involutive-eq p z q = p ∙ₗ⁻ q

  lconcat-involutive-eq' : (x : A) {y z : A} → y ＝⁻ z → x ＝⁻ y → x ＝⁻ z
  lconcat-involutive-eq' x q p = p ∙ₗ⁻ q

  eq-concat-lconcat-involutive-Id :
    {x y z : A} (p : x ＝⁻ y) (q : y ＝⁻ z) → p ∙ₗ⁻ q ＝ p ∙⁻ q
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

  distributive-concat-involutive-eq-eq :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    involutive-eq-eq (p ∙ q) ＝ involutive-eq-eq p ∙⁻ involutive-eq-eq q
  distributive-concat-involutive-eq-eq refl q = refl

  distributive-lconcat-eq-involutive-eq :
    {x y z : A} (p : x ＝⁻ y) (q : y ＝⁻ z) →
    eq-involutive-eq (p ∙ₗ⁻ q) ＝ eq-involutive-eq p ∙ eq-involutive-eq q
  distributive-lconcat-eq-involutive-eq (z , p , q) (z' , p' , q') =
    ( ap
      ( _∙ p')
      ( ( distributive-inv-concat (q' ∙ inv p) q) ∙
        ( ap
          ( inv q ∙_)
          ( distributive-inv-concat q' (inv p) ∙ ap (_∙ inv q') (inv-inv p))) ∙
        ( inv (assoc (inv q) p (inv q'))))) ∙
    ( assoc (inv q ∙ p) (inv q') p')

  distributive-concat-eq-involutive-eq :
    {x y z : A} (p : x ＝⁻ y) (q : y ＝⁻ z) →
    eq-involutive-eq (p ∙⁻ q) ＝ eq-involutive-eq p ∙ eq-involutive-eq q
  distributive-concat-eq-involutive-eq (z , p , q) (z' , p' , q') =
    ( ap
      ( λ x → inv x ∙ p')
      ( eq-double-concat-rconcat-left-associated q' (inv p) q)) ∙
    ( distributive-lconcat-eq-involutive-eq (z , p , q) (z' , p' , q'))
```

### The groupoidal laws for the judgmentally involutive identity types

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc-involutive-eq :
    {x y z w : A} (p : x ＝⁻ y) (q : y ＝⁻ z) (r : z ＝⁻ w) →
    ((p ∙⁻ q) ∙⁻ r) ＝ (p ∙⁻ (q ∙⁻ r))
  assoc-involutive-eq (z , p , q) (z' , p' , q') (z'' , p'' , q'') =
    eq-pair-eq-pr2
      ( eq-pair-eq-pr2
        ( ( inv (assoc-rconcat (q'' ∙ᵣ inv p') (q' ∙ᵣ inv p) q)) ∙
          ( ap (_∙ᵣ q) (inv (assoc-rconcat (q'' ∙ᵣ inv p') q' (inv p))))))

  left-unit-involutive-eq :
    {x y : A} {p : x ＝⁻ y} → refl-involutive-Id ∙⁻ p ＝ p
  left-unit-involutive-eq = refl

  right-unit-involutive-eq :
    {x y : A} {p : x ＝⁻ y} → p ∙⁻ refl-involutive-Id ＝ p
  right-unit-involutive-eq {p = z , refl , q} =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 left-unit-rconcat)

  left-inv-involutive-eq :
    {x y : A} (p : x ＝⁻ y) → inv-involutive-eq p ∙⁻ p ＝ refl-involutive-Id
  left-inv-involutive-eq (z , refl , q) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-rconcat q))

  right-inv-involutive-eq :
    {x y : A} (p : x ＝⁻ y) → p ∙⁻ inv-involutive-eq p ＝ refl-involutive-Id
  right-inv-involutive-eq (z , p , refl) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (right-inv-rconcat p))

  distributive-inv-concat-involutive-eq :
    {x y : A} (p : x ＝⁻ y) {z : A} (q : y ＝⁻ z) →
    inv-involutive-eq (p ∙⁻ q) ＝ inv-involutive-eq q ∙⁻ inv-involutive-eq p
  distributive-inv-concat-involutive-eq (z , refl , refl) (z' , p' , refl) =
    eq-pair-eq-pr2 (eq-pair-eq-pr2 (inv left-unit-rconcat))
```

## References

- <https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ>
