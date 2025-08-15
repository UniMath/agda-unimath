# Isomorphisms of algebras of theories

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.isomorphisms-algebras-of-theories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.large-categories
open import category-theory.large-precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.equivalences
open import foundation.sets
open import foundation.subtypes
open import foundation.subtype-identity-principle
open import foundation.universe-levels
open import foundation.transport-along-equivalences
open import foundation.torsorial-type-families
open import foundation.fundamental-theorem-of-identity-types

open import foundation-core.transport-along-identifications
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.retractions
open import foundation-core.homotopies
open import foundation-core.identity-types

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

```agda
module _
  { l1 : Level} ( S : signature l1)
  { l2 : Level} ( T : Theory S l2)
  { l3 : Level} ( A B : Algebra S T l3)
  where

  is-iso-Algebra : (f : hom-Algebra S T A B) → UU (l1 ⊔ l3)
  is-iso-Algebra f =
    is-iso-Large-Precategory (Algebra-Large-Precategory S T) {X = A} {Y = B} f

  iso-Algebra : UU (l1 ⊔ l3)
  iso-Algebra = iso-Large-Precategory (Algebra-Large-Precategory S T) A B

  is-prop-is-iso-Algebra :
    (f : hom-Algebra S T A B) → is-prop (is-iso-Algebra f)
  is-prop-is-iso-Algebra =
    is-prop-is-iso-Large-Precategory (Algebra-Large-Precategory S T)

  is-iso-is-equiv-Algebra :
    (f : hom-Algebra S T A B) →
    is-iso-Algebra f →
    is-equiv-hom-Algebra S T A B f
  pr1 (pr1 (is-iso-is-equiv-Algebra f (g , p))) = map-hom-Algebra S T B A g
  pr2 (pr1 (is-iso-is-equiv-Algebra f (g , (p , q)))) =
    htpy-eq-hom-Algebra S T B B
    ( comp-hom-Algebra S T B A B f g)
    ( id-hom-Algebra S T B) p
  pr1 (pr2 (is-iso-is-equiv-Algebra f (g , p))) = map-hom-Algebra S T B A g
  pr2 (pr2 (is-iso-is-equiv-Algebra f (g , (p , q)))) =
    htpy-eq-hom-Algebra S T A A
    ( comp-hom-Algebra S T A B A g f)
    ( id-hom-Algebra S T A) q

  is-equiv-is-iso-Algebra :
    (f : hom-Algebra S T A B) → is-equiv-hom-Algebra S T A B f → is-iso-Algebra f
  pr1 (is-equiv-is-iso-Algebra f eq) = inv-equiv-hom-Algebra S T A B f eq
  pr1 (pr2 (is-equiv-is-iso-Algebra f eq)) =
    eq-htpy-hom-Algebra S T B B
    ( comp-hom-Algebra S T B A B f
      ( inv-equiv-hom-Algebra S T A B f eq))
    ( id-hom-Algebra S T B) (pr2 (pr1 eq))
  pr2 (pr2 (is-equiv-is-iso-Algebra f eq)) =
    eq-htpy-hom-Algebra S T A A
    ( comp-hom-Algebra S T A B A
      ( inv-equiv-hom-Algebra S T A B f eq) f)
    ( id-hom-Algebra S T A) (htpy ∙h pr2 (pr2 eq))
      where
      htpy : map-inv-is-equiv eq ∘ pr1 f ~ pr1 (pr2 eq) ∘ pr1 f
      htpy x = htpy-map-inv-equiv-retraction (pr1 f , eq) (pr2 eq) (pr1 f x)

  Eq-Algebra-equiv-Algebra :
    Eq-Algebra S T A B → Σ (hom-Algebra S T A B) (is-equiv-hom-Algebra S T A B)
  pr1 (pr1 (Eq-Algebra-equiv-Algebra ((f , eq) , p))) = f
  pr2 (pr1 (Eq-Algebra-equiv-Algebra ((f , eq) , p))) op v =
    {!   !} ∙
    pr2 (pr1 eq)
    ( pr2 (pr1 B) op
    ( map-tuple (pr1 (pr1 (Eq-Algebra-equiv-Algebra ((f , eq) , p)))) v))
  pr2 (Eq-Algebra-equiv-Algebra ((f , eq) , p)) = eq

  equiv-Algebra-Eq-Algebra :
    Σ (hom-Algebra S T A B) (is-equiv-hom-Algebra S T A B) → Eq-Algebra S T A B
  pr1 (equiv-Algebra-Eq-Algebra ((f , _) , eq)) = f , eq
  pr2 (equiv-Algebra-Eq-Algebra ((f , p) , eq)) g = eq-htpy htpy
    where
    htpy :
      map-tr-equiv
      ( λ v → (x : pr1 S) → tuple v (pr2 S x) → v)
      ( pr1 (equiv-Algebra-Eq-Algebra ((f , p) , eq))) (pr2 (pr1 A)) g ~
      pr2 (pr1 B) g
    htpy x = {!   !} ∙ {!   !}

  equiv-Eq-Algebra-equiv-Algebra :
    Eq-Algebra S T A B ≃ Σ (hom-Algebra S T A B) (is-equiv-hom-Algebra S T A B)
  pr1 equiv-Eq-Algebra-equiv-Algebra = Eq-Algebra-equiv-Algebra
  pr1 (pr1 (pr2 equiv-Eq-Algebra-equiv-Algebra)) = equiv-Algebra-Eq-Algebra
  pr2 (pr1 (pr2 equiv-Eq-Algebra-equiv-Algebra)) (f , p) =
    eq-type-subtype
    ( is-equiv-hom-Algebra-Prop S T A B)
    ( eq-htpy-hom-Algebra S T A B (pr1
      (( pr1 equiv-Eq-Algebra-equiv-Algebra ∘
        pr1 (pr1 (pr2 equiv-Eq-Algebra-equiv-Algebra)))
        ( f , p))) f (λ x → refl))
  pr1 (pr2 (pr2 equiv-Eq-Algebra-equiv-Algebra)) = equiv-Algebra-Eq-Algebra
  pr2 (pr2 (pr2 equiv-Eq-Algebra-equiv-Algebra)) (f , p) =
    eq-type-subtype
    ( tr-is-model-signature-equiv-Set-Prop S (pr1 A) (pr1 (pr1 B)) (pr2 (pr1 B)))
    (eq-type-subtype is-equiv-Prop (eq-htpy (λ x → refl)))

  equiv-iso-Eq-Algebra : Eq-Algebra S T A B ≃ iso-Algebra
  equiv-iso-Eq-Algebra =
    equiv-type-subtype
    ( is-prop-is-equiv-hom-Algebra S T A B)
    ( is-prop-is-iso-Algebra)
    ( is-equiv-is-iso-Algebra)
    ( is-iso-is-equiv-Algebra) ∘e {!   !}

module _
  { l1 : Level} ( S : signature l1)
  { l2 : Level} ( T : Theory S l2)
  { l3 : Level} ( A : Algebra S T l3)
  where

  is-torsorial-iso-Algebra : is-torsorial (iso-Algebra S T A)
  is-torsorial-iso-Algebra =
    is-contr-equiv'
    ( Σ (Algebra S T l3) (Eq-Algebra S T A))
    ( equiv-tot (equiv-iso-Eq-Algebra S T A))
    ( is-torsorial-Eq-Algebra S T A)
```
