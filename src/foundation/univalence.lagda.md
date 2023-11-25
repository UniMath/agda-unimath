# The univalence axiom

```agda
module foundation.univalence where

open import foundation-core.univalence public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The univalence axiom characterizes the
[identity types](foundation-core.identity-types.md) of universes. It asserts
that the map `(A ＝ B) → (A ≃ B)` is an
[equivalence](foundation-core.equivalences.md).

In this file we postulate the univalence axiom. Its statement is defined in
[`foundation-core.univalence`](foundation-core.univalence.md).

## Postulate

```agda
postulate
  univalence : univalence-axiom
```

## Properties

```agda
module _
  {l : Level}
  where

  equiv-univalence :
    {A B : UU l} → (A ＝ B) ≃ (A ≃ B)
  pr1 equiv-univalence = equiv-eq
  pr2 (equiv-univalence {A} {B}) = univalence A B

  eq-equiv : (A B : UU l) → A ≃ B → A ＝ B
  eq-equiv A B = map-inv-is-equiv (univalence A B)

  abstract
    is-section-eq-equiv :
      {A B : UU l} → (equiv-eq ∘ eq-equiv A B) ~ id
    is-section-eq-equiv {A} {B} = is-section-map-inv-is-equiv (univalence A B)

    is-retraction-eq-equiv :
      {A B : UU l} → (eq-equiv A B ∘ equiv-eq) ~ id
    is-retraction-eq-equiv {A} {B} =
      is-retraction-map-inv-is-equiv (univalence A B)

    is-equiv-eq-equiv :
      (A B : UU l) → is-equiv (eq-equiv A B)
    is-equiv-eq-equiv A B = is-equiv-map-inv-is-equiv (univalence A B)

    compute-eq-equiv-id-equiv :
      (A : UU l) → eq-equiv A A id-equiv ＝ refl
    compute-eq-equiv-id-equiv A = is-retraction-eq-equiv refl

    equiv-eq-equiv :
      (A B : UU l) → (A ≃ B) ≃ (A ＝ B)
    pr1 (equiv-eq-equiv A B) = eq-equiv A B
    pr2 (equiv-eq-equiv A B) = is-equiv-eq-equiv A B
```

### The total space of all equivalences out of a type or into a type is contractible

Type families of which the [total space](foundation.dependent-pair-types.md) is
[contractible](foundation-core.contractible-types.md) are also called
[torsorial](foundation-core.torsorial-type-families.md). This terminology
originates from higher group theory, where a
[higher group action](higher-group-theory.higher-group-actions.md) is torsorial
if its type of [orbits](higher-group-theory.orbits-higher-group-actions.md),
i.e., its total space, is contractible. Our claim that the total space of all
equivalences out of a type `A` is contractible can therefore be stated more
succinctly as the claim that the family of equivalences out of `A` is torsorial.

```agda
  abstract
    is-torsorial-equiv :
      (A : UU l) → is-torsorial (λ (X : UU l) → A ≃ X)
    is-torsorial-equiv A =
      is-torsorial-equiv-based-univalence A (univalence A)

    is-torsorial-equiv' :
      (A : UU l) → is-torsorial (λ (X : UU l) → X ≃ A)
    is-torsorial-equiv' A =
      is-contr-equiv'
        ( Σ (UU l) (λ X → X ＝ A))
        ( equiv-tot (λ X → equiv-univalence))
        ( is-torsorial-path' A)
```

### Univalence for type families

```agda
equiv-fam :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
equiv-fam {A = A} B C = (a : A) → B a ≃ C a

id-equiv-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → equiv-fam B B
id-equiv-fam B a = id-equiv

equiv-eq-fam :
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → B ＝ C → equiv-fam B C
equiv-eq-fam B .B refl = id-equiv-fam B

abstract
  is-torsorial-equiv-fam :
    {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
    is-torsorial (λ (C : A → UU l2) → equiv-fam B C)
  is-torsorial-equiv-fam B =
    is-torsorial-Eq-Π
      ( λ x X → (B x) ≃ X)
      ( λ x → is-torsorial-equiv (B x))

abstract
  is-equiv-equiv-eq-fam :
    {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → is-equiv (equiv-eq-fam B C)
  is-equiv-equiv-eq-fam B =
    fundamental-theorem-id
      ( is-torsorial-equiv-fam B)
      ( equiv-eq-fam B)

extensionality-fam :
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → (B ＝ C) ≃ equiv-fam B C
pr1 (extensionality-fam B C) = equiv-eq-fam B C
pr2 (extensionality-fam B C) = is-equiv-equiv-eq-fam B C

eq-equiv-fam :
  {l1 l2 : Level} {A : UU l1} {B C : A → UU l2} → equiv-fam B C → B ＝ C
eq-equiv-fam {B = B} {C} = map-inv-is-equiv (is-equiv-equiv-eq-fam B C)
```

### Computations with univalence

```agda
compute-equiv-eq-concat :
  {l : Level} {A B C : UU l} (p : A ＝ B) (q : B ＝ C) →
  ((equiv-eq q) ∘e (equiv-eq p)) ＝ equiv-eq (p ∙ q)
compute-equiv-eq-concat refl refl = eq-equiv-eq-map-equiv refl

compute-eq-equiv-comp-equiv :
  {l : Level} (A B C : UU l) (f : A ≃ B) (g : B ≃ C) →
  ((eq-equiv A B f) ∙ (eq-equiv B C g)) ＝ eq-equiv A C (g ∘e f)
compute-eq-equiv-comp-equiv A B C f g =
  is-injective-map-equiv
    ( equiv-univalence)
    ( ( inv ( compute-equiv-eq-concat (eq-equiv A B f) (eq-equiv B C g))) ∙
      ( ( ap
          ( λ e → (map-equiv e g) ∘e (equiv-eq (eq-equiv A B f)))
          ( right-inverse-law-equiv equiv-univalence)) ∙
        ( ( ap
            ( λ e → g ∘e map-equiv e f)
            ( right-inverse-law-equiv equiv-univalence)) ∙
          ( ap
            ( λ e → map-equiv e (g ∘e f))
            ( inv (right-inverse-law-equiv equiv-univalence))))))

compute-equiv-eq-ap-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A} (p : x ＝ y) →
  map-equiv (equiv-eq (ap B (inv p)) ∘e (equiv-eq (ap B p))) ~ id
compute-equiv-eq-ap-inv refl = refl-htpy

commutativity-inv-equiv-eq :
  {l : Level} (A B : UU l) (p : A ＝ B) →
  inv-equiv (equiv-eq p) ＝ equiv-eq (inv p)
commutativity-inv-equiv-eq A .A refl = eq-equiv-eq-map-equiv refl

commutativity-inv-eq-equiv :
  {l : Level} (A B : UU l) (f : A ≃ B) →
  inv (eq-equiv A B f) ＝ eq-equiv B A (inv-equiv f)
commutativity-inv-eq-equiv A B f =
  is-injective-map-equiv
    ( equiv-univalence)
    ( ( inv (commutativity-inv-equiv-eq A B (eq-equiv A B f))) ∙
      ( ( ap
          ( λ e → (inv-equiv (map-equiv e f)))
          ( right-inverse-law-equiv equiv-univalence)) ∙
        ( ap
          ( λ e → map-equiv e (inv-equiv f))
          ( inv (right-inverse-law-equiv equiv-univalence)))))
```
