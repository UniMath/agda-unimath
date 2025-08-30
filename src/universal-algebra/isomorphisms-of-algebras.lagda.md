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
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.injective-maps
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.precategory-of-algebras-of-theories
open import universal-algebra.signatures
```

</details>

## Idea

We characterize
[isomorphisms](category-theory.isomorphisms-in-large-precategories.md) of
[algebras of theories](universal-algebra.precategory-of-algebras-of-theories.md).

## Definition

### The property that a homomorphism of algebras is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Theory σ l2)
  (A : Algebra σ T l3)
  (B : Algebra σ T l4)
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

### The inverse of an equivalence of algebras

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Theory σ l2)
  (A : Algebra σ T l3)
  (B : Algebra σ T l4)
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
                    Eq-tuple n w (map-tuple
                      (map-hom-Algebra σ T A B f)
                      (map-tuple (map-inv-is-equiv eq) w))
                  eq2 zero-ℕ empty-tuple = map-raise star
                  pr1 (eq2 (succ-ℕ n) (x ∷ w)) =
                    inv (is-section-map-section-is-equiv eq x)
                  pr2 (eq2 (succ-ℕ n) (x ∷ w)) = eq2 n w

  hom-inv-is-equiv-hom-Algebra : hom-Algebra σ T B A
  pr1 hom-inv-is-equiv-hom-Algebra =
    map-inv-is-equiv eq
  pr2 hom-inv-is-equiv-hom-Algebra =
    preserves-operations-map-hom-inv-is-equiv-hom-Algebra
```

## Proof

### A useful factorization for characterizing isomorphisms of algebras

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1) (T : Theory σ l2) (A : Algebra σ T l3)
  where

  equiv-equiv-hom-Algebra' :
    (B : Algebra σ T l3) → equiv-hom-Algebra σ T A B ≃
    Σ (hom-Set (set-Algebra σ T A) (set-Algebra σ T B))
      (λ f → (is-equiv f) × preserves-operations-Algebra σ T A B f)
  pr1 (equiv-equiv-hom-Algebra' B) ((f , p) , eq) = (f , eq , p)
  pr1 (pr1 (pr2 (equiv-equiv-hom-Algebra' B))) (f , eq , p) = ((f , p) , eq)
  pr2 (pr1 (pr2 (equiv-equiv-hom-Algebra' B))) _ = refl
  pr1 (pr2 (pr2 (equiv-equiv-hom-Algebra' B))) (f , eq , p) = ((f , p) , eq)
  pr2 (pr2 (pr2 (equiv-equiv-hom-Algebra' B))) _ = refl
```

### Characterizing isomorphisms of algebras

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1) (T : Theory σ l2) (A B : Algebra σ T l3)
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
  pr1 (pr1 (is-equiv-hom-is-iso-Algebra f (g , p))) = map-hom-Algebra σ T B A g
  pr2 (pr1 (is-equiv-hom-is-iso-Algebra f (g , (p , q)))) =
    htpy-eq-hom-Algebra σ T B B
      ( comp-hom-Algebra σ T B A B f g)
      ( id-hom-Algebra σ T B)
      ( p)
  pr1 (pr2 (is-equiv-hom-is-iso-Algebra f (g , p))) = map-hom-Algebra σ T B A g
  pr2 (pr2 (is-equiv-hom-is-iso-Algebra f (g , (p , q)))) =
    htpy-eq-hom-Algebra σ T A A
      ( comp-hom-Algebra σ T A B A g f)
      ( id-hom-Algebra σ T A)
      ( q)

  is-iso-is-equiv-hom-Algebra :
    (f : hom-Algebra σ T A B) →
    is-equiv-hom-Algebra σ T A B f →
    is-iso-Algebra f
  pr1 (is-iso-is-equiv-hom-Algebra f eq) =
    hom-inv-is-equiv-hom-Algebra σ T A B f eq
  pr1 (pr2 (is-iso-is-equiv-hom-Algebra f eq)) =
    eq-htpy-hom-Algebra σ T B B
    ( comp-hom-Algebra σ T B A B f
      ( hom-inv-is-equiv-hom-Algebra σ T A B f eq))
    ( id-hom-Algebra σ T B)
    ( is-section-map-section-map-equiv ((map-hom-Algebra σ T A B f) , eq))
  pr2 (pr2 (is-iso-is-equiv-hom-Algebra f eq)) =
    eq-htpy-hom-Algebra σ T A A
      ( comp-hom-Algebra σ T A B A
        ( hom-inv-is-equiv-hom-Algebra σ T A B f eq)
        ( f))
      ( id-hom-Algebra σ T A)
      ( htpy ∙h
        is-retraction-map-retraction-map-equiv (map-hom-Algebra σ T A B f , eq))
      where
      htpy :
        map-inv-is-equiv eq ∘
          map-hom-Algebra σ T A B f ~
        map-retraction-map-equiv ((map-hom-Algebra σ T A B f) , eq) ∘
          map-equiv ((map-hom-Algebra σ T A B f) , eq)
      htpy x =
        htpy-map-inv-equiv-retraction
          ( map-hom-Algebra σ T A B f , eq)
          ( retraction-is-equiv eq)
          ( map-hom-Algebra σ T A B f x)

  equiv-iso-Eq-Algebra : Eq-Algebra σ T A B ≃ iso-Algebra
  equiv-iso-Eq-Algebra =
    equiv-type-subtype
      ( is-prop-is-equiv-hom-Algebra σ T A B)
      ( is-prop-is-iso-Algebra)
      ( is-iso-is-equiv-hom-Algebra)
      ( is-equiv-hom-is-iso-Algebra) ∘e
      ( inv-equiv (equiv-equiv-hom-Algebra' σ T A B)) ∘e
      ( equiv-Eq-Model-Signature' σ (model-Algebra σ T A) (model-Algebra σ T B))

  iso-Eq-Algebra : Eq-Algebra σ T A B → iso-Algebra
  iso-Eq-Algebra = map-equiv equiv-iso-Eq-Algebra

  is-equiv-iso-Eq-Algebra : is-equiv iso-Eq-Algebra
  is-equiv-iso-Eq-Algebra = is-equiv-map-equiv equiv-iso-Eq-Algebra

module _
  {l1 l2 l3 : Level} (σ : signature l1) (T : Theory σ l2) (A : Algebra σ T l3)
  where

  is-torsorial-iso-Algebra : is-torsorial (iso-Algebra σ T A)
  is-torsorial-iso-Algebra =
    is-contr-equiv'
      ( Σ (Algebra σ T l3) (Eq-Algebra σ T A))
      ( equiv-tot (equiv-iso-Eq-Algebra σ T A))
      ( is-torsorial-Eq-Algebra σ T A)

  is-equiv-iso-eq-Algebra :
    (B : Algebra σ T l3) →
    is-equiv (iso-eq-Large-Precategory (Algebra-Large-Precategory σ T) A B)
  is-equiv-iso-eq-Algebra =
    fundamental-theorem-id
      ( is-torsorial-iso-Algebra)
      ( iso-eq-Large-Precategory (Algebra-Large-Precategory σ T) A)
```
