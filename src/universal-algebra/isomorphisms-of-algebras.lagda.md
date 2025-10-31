# Isomorphisms of algebras of theories

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.isomorphisms-of-algebras where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-precategories

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.injective-maps
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-algebraic-theories
open import universal-algebra.equivalences-models-of-signatures
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.precategory-of-algebras-algebraic-theories
open import universal-algebra.signatures
```

</details>

## Idea

We characterize
[isomorphisms](category-theory.isomorphisms-in-large-precategories.md) of
[algebras](universal-algebra.precategory-of-algebras-algebraic-theories.md) of
[algebraic theories](universal-algebra.algebraic-theories.md).

## Definitions

### The property that a homomorphism of algebras is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (B : Algebra l4 σ T)
  where

  is-equiv-hom-Algebra : (f : hom-Algebra σ T A B) → UU (l3 ⊔ l4)
  is-equiv-hom-Algebra f = is-equiv (map-hom-Algebra σ T A B f)

  is-prop-is-equiv-hom-Algebra :
    (f : hom-Algebra σ T A B) → is-prop (is-equiv-hom-Algebra f)
  is-prop-is-equiv-hom-Algebra f = is-property-is-equiv (pr1 f)

  is-equiv-hom-prop-Algebra : (f : hom-Algebra σ T A B) → Prop (l3 ⊔ l4)
  pr1 (is-equiv-hom-prop-Algebra f) = is-equiv-hom-Algebra f
  pr2 (is-equiv-hom-prop-Algebra f) = is-prop-is-equiv-hom-Algebra f

  equiv-hom-Algebra : UU (l1 ⊔ l3 ⊔ l4)
  equiv-hom-Algebra = Σ (hom-Algebra σ T A B) is-equiv-hom-Algebra
```

### Equivalences of algebras

```agda
module _
  {l1 l2 l3 l4 : Level} (σ : signature l1) (T : Algebraic-Theory l2 σ)
  where

  equiv-Algebra : (A : Algebra l3 σ T) (B : Algebra l4 σ T) → UU (l1 ⊔ l3 ⊔ l4)
  equiv-Algebra A B =
    equiv-Model σ (model-Algebra σ T A) (model-Algebra σ T B)
```

### The inverse of an equivalence of algebras

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (B : Algebra l4 σ T)
  (f : hom-Algebra σ T A B)
  (eq : is-equiv (map-hom-Algebra σ T A B f))
  where

  preserves-operations-map-hom-inv-is-equiv-hom-Algebra :
    preserves-operations-Algebra σ T B A
      (map-inv-equiv ((map-hom-Algebra σ T A B f) , eq))
  preserves-operations-map-hom-inv-is-equiv-hom-Algebra op v =
    is-injective-is-equiv eq
      ( is-section-map-inv-is-equiv eq
        ( is-model-set-Algebra σ T B op v) ∙
          ( ap
            ( is-model-set-Algebra σ T B op)
            ( eq-Eq-tuple
              ( arity-operation-signature σ op)
              ( v)
              ( map-tuple
                ( map-hom-Algebra σ T A B f)
                ( map-tuple (map-inv-is-equiv eq) v))
              ( eq2 (arity-operation-signature σ op) v)) ∙
            ( inv
              ( preserves-operations-hom-Algebra σ T A B f op
                ( map-tuple (map-inv-is-equiv eq) v)))))
    where
    eq2 : (n : ℕ) (w : tuple (type-Algebra σ T B) n) →
      Eq-tuple n w
        ( map-tuple
          ( map-hom-Algebra σ T A B f)
          ( map-tuple (map-inv-is-equiv eq) w))
    eq2 zero-ℕ empty-tuple = map-raise star
    pr1 (eq2 (succ-ℕ n) (x ∷ w)) = inv (is-section-map-section-is-equiv eq x)
    pr2 (eq2 (succ-ℕ n) (x ∷ w)) = eq2 n w

  hom-inv-is-equiv-hom-Algebra : hom-Algebra σ T B A
  pr1 hom-inv-is-equiv-hom-Algebra =
    map-inv-is-equiv eq
  pr2 hom-inv-is-equiv-hom-Algebra =
    preserves-operations-map-hom-inv-is-equiv-hom-Algebra
```

## Properties

### Equivalences characterize equality of algebras

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (T : Algebraic-Theory l2 σ)
  where

  equiv-eq-Algebra :
    {l3 : Level} (A B : Algebra l3 σ T) → A ＝ B → equiv-Algebra σ T A B
  equiv-eq-Algebra A .A refl =
    id-equiv-Model σ (model-Algebra σ T A)

  is-equiv-equiv-eq-Algebra :
    {l3 : Level} (A B : Algebra l3 σ T) →
    is-equiv (equiv-eq-Algebra A B)
  is-equiv-equiv-eq-Algebra (A , p) =
    subtype-identity-principle
      ( is-prop-is-algebra σ T)
      ( p)
      ( id-equiv-Model σ A)
      ( equiv-eq-Algebra (A , p))
      ( is-equiv-equiv-eq-Model σ A)

  extensionality-Algebra :
    {l3 : Level} (A B : Algebra l3 σ T) →
    (A ＝ B) ≃ equiv-Algebra σ T A B
  extensionality-Algebra A B =
    ( equiv-eq-Algebra A B , is-equiv-equiv-eq-Algebra A B)

  eq-equiv-Algebra :
    {l3 : Level} (A B : Algebra l3 σ T) →
    equiv-Algebra σ T A B → A ＝ B
  eq-equiv-Algebra A B = map-inv-equiv (extensionality-Algebra A B)

  abstract
    is-torsorial-equiv-Algebra :
      {l3 : Level} (A : Algebra l3 σ T) →
      is-torsorial (equiv-Algebra {l4 = l3} σ T A)
    is-torsorial-equiv-Algebra A =
      fundamental-theorem-id'
        ( equiv-eq-Algebra A)
        ( λ B → is-equiv-equiv-eq-Algebra A B)
```

### A useful factorization for characterizing isomorphisms of algebras

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (T : Algebraic-Theory l2 σ) (A : Algebra l3 σ T)
  where

  equiv-equiv-hom-Algebra' :
    {l4 : Level}
    (B : Algebra l4 σ T) →
    equiv-hom-Algebra σ T A B ≃
    Σ ( type-Algebra σ T A → type-Algebra σ T B)
      ( λ f → (is-equiv f) × preserves-operations-Algebra σ T A B f)
  pr1 (equiv-equiv-hom-Algebra' B) ((f , p) , eq) = (f , eq , p)
  pr1 (pr1 (pr2 (equiv-equiv-hom-Algebra' B))) (f , eq , p) = ((f , p) , eq)
  pr2 (pr1 (pr2 (equiv-equiv-hom-Algebra' B))) _ = refl
  pr1 (pr2 (pr2 (equiv-equiv-hom-Algebra' B))) (f , eq , p) = ((f , p) , eq)
  pr2 (pr2 (pr2 (equiv-equiv-hom-Algebra' B))) _ = refl
```

### Characterizing isomorphisms of algebras

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (T : Algebraic-Theory l2 σ) (A B : Algebra l3 σ T)
  where

  is-iso-Algebra : (f : hom-Algebra σ T A B) → UU (l1 ⊔ l3)
  is-iso-Algebra f =
    is-iso-Large-Precategory (Algebra-Large-Precategory σ T) {X = A} {Y = B} f

  iso-Algebra : UU (l1 ⊔ l3)
  iso-Algebra = iso-Large-Precategory (Algebra-Large-Precategory σ T) A B

  is-prop-is-iso-Algebra :
    (f : hom-Algebra σ T A B) → is-prop (is-iso-Algebra f)
  is-prop-is-iso-Algebra =
    is-prop-is-iso-Large-Precategory (Algebra-Large-Precategory σ T)

  is-equiv-hom-is-iso-Algebra :
    (f : hom-Algebra σ T A B) →
    is-iso-Algebra f →
    is-equiv-hom-Algebra σ T A B f
  is-equiv-hom-is-iso-Algebra f (g , (p , q)) =
    is-equiv-is-invertible
      ( map-hom-Algebra σ T B A g)
      ( htpy-eq-hom-Algebra σ T B B
        ( comp-hom-Algebra σ T B A B f g)
        ( id-hom-Algebra σ T B)
        ( p))
      ( htpy-eq-hom-Algebra σ T A A
        ( comp-hom-Algebra σ T A B A g f)
        ( id-hom-Algebra σ T A)
        ( q))

  is-split-epi-is-equiv-hom-Algebra :
    (f : hom-Algebra σ T A B) (eq : is-equiv-hom-Algebra σ T A B f) →
    comp-hom-Algebra σ T A B A (hom-inv-is-equiv-hom-Algebra σ T A B f eq) f ＝
    id-hom-Algebra σ T A
  is-split-epi-is-equiv-hom-Algebra f eq =
    eq-htpy-hom-Algebra σ T A A
      ( comp-hom-Algebra σ T A B A
        ( hom-inv-is-equiv-hom-Algebra σ T A B f eq)
        ( f))
      ( id-hom-Algebra σ T A)
      ( ( htpy-map-inv-equiv-retraction
          ( map-hom-Algebra σ T A B f , eq)
          ( retraction-is-equiv eq) ·r
          ( map-hom-Algebra σ T A B f)) ∙h
        ( is-retraction-map-retraction-map-equiv
          ( map-hom-Algebra σ T A B f , eq)))

  is-split-mono-is-equiv-hom-Algebra :
    (f : hom-Algebra σ T A B) (eq : is-equiv-hom-Algebra σ T A B f) →
    comp-hom-Algebra σ T B A B f (hom-inv-is-equiv-hom-Algebra σ T A B f eq) ＝
    id-hom-Algebra σ T B
  is-split-mono-is-equiv-hom-Algebra f eq =
    eq-htpy-hom-Algebra σ T B B
    ( comp-hom-Algebra σ T B A B f
      ( hom-inv-is-equiv-hom-Algebra σ T A B f eq))
    ( id-hom-Algebra σ T B)
    ( is-section-map-section-map-equiv ((map-hom-Algebra σ T A B f) , eq))

  is-iso-is-equiv-hom-Algebra :
    (f : hom-Algebra σ T A B) →
    is-equiv-hom-Algebra σ T A B f →
    is-iso-Algebra f
  is-iso-is-equiv-hom-Algebra f eq =
    ( hom-inv-is-equiv-hom-Algebra σ T A B f eq ,
      is-split-mono-is-equiv-hom-Algebra f eq ,
      is-split-epi-is-equiv-hom-Algebra f eq)

  equiv-iso-equiv-Algebra : equiv-Algebra σ T A B ≃ iso-Algebra
  equiv-iso-equiv-Algebra =
    ( equiv-type-subtype
      ( is-prop-is-equiv-hom-Algebra σ T A B)
      ( is-prop-is-iso-Algebra)
      ( is-iso-is-equiv-hom-Algebra)
      ( is-equiv-hom-is-iso-Algebra)) ∘e
    ( inv-equiv (equiv-equiv-hom-Algebra' σ T A B)) ∘e
    ( associative-Σ)

  iso-equiv-Algebra : equiv-Algebra σ T A B → iso-Algebra
  iso-equiv-Algebra = map-equiv equiv-iso-equiv-Algebra

  is-equiv-iso-equiv-Algebra : is-equiv iso-equiv-Algebra
  is-equiv-iso-equiv-Algebra = is-equiv-map-equiv equiv-iso-equiv-Algebra

module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (T : Algebraic-Theory l2 σ) (A : Algebra l3 σ T)
  where abstract

  is-torsorial-iso-Algebra : is-torsorial (iso-Algebra σ T A)
  is-torsorial-iso-Algebra =
    is-contr-equiv'
      ( Σ (Algebra l3 σ T) (equiv-Algebra σ T A))
      ( equiv-tot (equiv-iso-equiv-Algebra σ T A))
      ( is-torsorial-equiv-Algebra σ T A)

  is-equiv-iso-eq-Algebra :
    (B : Algebra l3 σ T) →
    is-equiv (iso-eq-Large-Precategory (Algebra-Large-Precategory σ T) A B)
  is-equiv-iso-eq-Algebra =
    fundamental-theorem-id
      ( is-torsorial-iso-Algebra)
      ( iso-eq-Large-Precategory (Algebra-Large-Precategory σ T) A)
```
