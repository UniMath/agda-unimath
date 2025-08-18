# Homomorphisms of algebras

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.homomorphisms-of-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.subtypes

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

An algebra homomorphism from one algebra to another is a function between their
underlying types such that all the structure is preserved.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Theory σ l2)
  (A : Algebra σ T l3)
  (B : Algebra σ T l4)
  where

  preserves-operations-Algebra :
    (type-Algebra σ T A → type-Algebra σ T B) →
    UU (l1 ⊔ l3 ⊔ l4)
  preserves-operations-Algebra f =
    ( op : operation-signature σ) →
    ( v : tuple (type-Algebra σ T A)
      ( arity-operation-signature σ op)) →
        ( f (is-model-set-Algebra σ T A op v) ＝
          ( is-model-set-Algebra σ T B op (map-tuple f v)))

  is-prop-preserves-operations-Algebra :
    (f : type-Algebra σ T A → type-Algebra σ T B) →
    is-prop (preserves-operations-Algebra f)
  is-prop-preserves-operations-Algebra f =
    is-prop-Π
      ( λ x →
        is-prop-Π
          ( λ y → is-set-type-Algebra σ T B
            ( f (is-model-set-Algebra σ T A x y))
            ( is-model-set-Algebra σ T B x (map-tuple f y))))

  preserves-operations-Algebra-Prop :
    (f : type-Algebra σ T A → type-Algebra σ T B) →
    Prop (l1 ⊔ l3 ⊔ l4)
  preserves-operations-Algebra-Prop f =
    ( preserves-operations-Algebra f) , (is-prop-preserves-operations-Algebra f)

  hom-Algebra : UU (l1 ⊔ l3 ⊔ l4)
  hom-Algebra =
    Σ ( type-Algebra σ T A → type-Algebra σ T B)
      ( preserves-operations-Algebra)

  map-hom-Algebra :
    hom-Algebra →
    type-Algebra σ T A →
    type-Algebra σ T B
  map-hom-Algebra = pr1

  preserves-operations-hom-Algebra :
    ( f : hom-Algebra) →
    preserves-operations-Algebra (map-hom-Algebra f)
  preserves-operations-hom-Algebra = pr2

  hom-Algebra-Subtype :
    subtype (l1 ⊔ l3 ⊔ l4) (type-Algebra σ T A → type-Algebra σ T B)
  hom-Algebra-Subtype = preserves-operations-Algebra-Prop
```

### Composition of algebra homomorphisms

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (σ : signature l1)
  (T : Theory σ l2)
  (A : Algebra σ T l3)
  (B : Algebra σ T l4)
  (C : Algebra σ T l5)
  where

  preserves-operations-map-comp-hom-Algebra :
    (g : hom-Algebra σ T B C) (f : hom-Algebra σ T A B) →
    preserves-operations-Algebra σ T A C
      (map-hom-Algebra σ T B C g ∘ map-hom-Algebra σ T A B f)
  preserves-operations-map-comp-hom-Algebra (g , q) (f , p) op v =
    equational-reasoning
    (g ∘ f) (is-model-set-Algebra σ T A op v)
    ＝ g (is-model-set-Algebra σ T B op (map-tuple f v))
      by ap g (p op v)
    ＝ is-model-set-Algebra σ T C op (map-tuple g (map-tuple f v))
      by q op (map-tuple f v)
    ＝ is-model-set-Algebra σ T C op
      (map-tuple (g ∘ f) v)
      by ap (is-model-set-Algebra σ T C op)
      ( preserves-comp-map-tuple (arity-operation-signature σ op) f g v)

  comp-hom-Algebra :
    (g : hom-Algebra σ T B C) (f : hom-Algebra σ T A B) →
    hom-Algebra σ T A C
  pr1 (comp-hom-Algebra (g , _) (f , _)) = g ∘ f
  pr2 (comp-hom-Algebra g f) op v =
    preserves-operations-map-comp-hom-Algebra g f op v

```

## Properties

### The type of algebra homomorphisms for any theory is a set

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Theory σ l2)
  (A : Algebra σ T l3)
  (B : Algebra σ T l4)
  where

  is-set-hom-Algebra : is-set (hom-Algebra σ T A B)
  is-set-hom-Algebra =
    is-set-type-subtype
    ( hom-Algebra-Subtype σ T A B)
    ( is-set-hom-Set (set-Algebra σ T A) (set-Algebra σ T B))

  set-hom-Algebra : Set (l1 ⊔ l3 ⊔ l4)
  set-hom-Algebra = (hom-Algebra σ T A B) , is-set-hom-Algebra

  htpy-hom-Algebra : (f g : hom-Algebra σ T A B) → UU (l3 ⊔ l4)
  htpy-hom-Algebra (f , _) (g , _) = f ~ g

  htpy-eq-hom-Algebra :
    (f g : hom-Algebra σ T A B) → f ＝ g → htpy-hom-Algebra f g
  htpy-eq-hom-Algebra f .f refl x = refl

  is-equiv-htpy-eq-hom-Algebra :
    (f g : hom-Algebra σ T A B) → is-equiv (htpy-eq-hom-Algebra f g)
  is-equiv-htpy-eq-hom-Algebra (f , p) =
    subtype-identity-principle
      ( is-prop-preserves-operations-Algebra σ T A B)
      ( p)
      ( refl-htpy)
      ( htpy-eq-hom-Algebra (f , p))
      ( funext f)

  equiv-htpy-eq-hom-Algebra :
    (f g : hom-Algebra σ T A B) → (f ＝ g) ≃ (htpy-hom-Algebra f g)
  equiv-htpy-eq-hom-Algebra f g =
    ( htpy-eq-hom-Algebra f g , is-equiv-htpy-eq-hom-Algebra f g)

  eq-htpy-hom-Algebra :
    (f g : hom-Algebra σ T A B) → htpy-hom-Algebra f g → f ＝ g
  eq-htpy-hom-Algebra f g = map-inv-equiv (equiv-htpy-eq-hom-Algebra f g)

  refl-htpy-hom-Algebra :
    (f : hom-Algebra σ T A B) → htpy-hom-Algebra f f
  refl-htpy-hom-Algebra f = refl-htpy
```

### The identity map is an algebra homomorphism

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1) (T : Theory σ l2) (A : Algebra σ T l3)
  where

  is-hom-id-Algebra : preserves-operations-Algebra σ T A A id
  is-hom-id-Algebra op v =
    ap
      ( is-model-set-Algebra σ T A op)
      ( preserves-id-map-tuple (arity-operation-signature σ op) v)

  id-hom-Algebra : hom-Algebra σ T A A
  id-hom-Algebra = (id , is-hom-id-Algebra)
```

### Composition of algebra homomorphisms is associative

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (σ : signature l1)
  (T : Theory σ l2)
  (A : Algebra σ T l3)
  (B : Algebra σ T l4)
  (C : Algebra σ T l5)
  (D : Algebra σ T l6)
  where

  associative-comp-hom-Algebra :
    (h : hom-Algebra σ T C D)
    (g : hom-Algebra σ T B C)
    (f : hom-Algebra σ T A B) →
    comp-hom-Algebra σ T A B D
      ( comp-hom-Algebra σ T B C D h g) f ＝
    comp-hom-Algebra σ T A C D h
      ( comp-hom-Algebra σ T A B C g f)
  associative-comp-hom-Algebra h g f =
    eq-htpy-hom-Algebra σ T A D
    ( comp-hom-Algebra σ T A B D
      ( comp-hom-Algebra σ T B C D h g) f)
    ( comp-hom-Algebra σ T A C D h
      ( comp-hom-Algebra σ T A B C g f))
    ( refl-htpy)
```

### Left and right unit laws for homomorphism composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Theory σ l2)
  (A : Algebra σ T l3)
  (B : Algebra σ T l4)
  where

  left-unit-law-comp-hom-Algebra :
    (f : hom-Algebra σ T A B) →
    comp-hom-Algebra σ T A B B (id-hom-Algebra σ T B) f ＝ f
  left-unit-law-comp-hom-Algebra f =
    eq-htpy-hom-Algebra σ T A B
    ( comp-hom-Algebra σ T A B B (id-hom-Algebra σ T B) f) f
    ( refl-htpy)

  right-unit-law-comp-hom-Algebra :
    (f : hom-Algebra σ T A B) →
    comp-hom-Algebra σ T A A B f (id-hom-Algebra σ T A) ＝ f
  right-unit-law-comp-hom-Algebra f =
    eq-htpy-hom-Algebra σ T A B
      ( comp-hom-Algebra σ T A A B f (id-hom-Algebra σ T A)) f
      ( refl-htpy)
```
