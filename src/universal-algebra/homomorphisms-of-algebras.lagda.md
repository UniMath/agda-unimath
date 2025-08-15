# Homomorphisms of algebras

```agda
module universal-algebra.homomorphisms-of-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.subtype-identity-principle
open import foundation.universe-levels
open import foundation.sets

open import foundation.action-on-identifications-functions
open import foundation-core.identity-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.subtypes
open import foundation-core.propositions

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.signatures
```

</details>

## Idea

An algebra homomorphism from one algebra to another is a function between their
underlying types such that all the structure is preserved.

## Definitions

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 : Level}
  ( Alg1 : Algebra Sg Th l3)
  ( Alg2 : Algebra Sg Th l4)
  where

  preserves-operations-Algebra :
    (type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2) →
    UU (l1 ⊔ l3 ⊔ l4)
  preserves-operations-Algebra f =
    ( op : operation-signature Sg) →
    ( v : tuple (type-Algebra Sg Th Alg1)
      ( arity-operation-signature Sg op)) →
        ( f (is-model-set-Algebra Sg Th Alg1 op v) ＝
          ( is-model-set-Algebra Sg Th Alg2 op (map-tuple f v)))

  is-prop-preserves-operations-Algebra :
    (f : type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2) →
    is-prop (preserves-operations-Algebra f)
  is-prop-preserves-operations-Algebra f =
    is-prop-Π (λ x →
      is-prop-Π (λ y → pr2 (pr1 (pr1 Alg2)) (f (pr2 (pr1 Alg1) x y))
        (pr2 (pr1 Alg2) x (map-tuple f y))))

  preserves-operations-Algebra-Prop :
    (f : type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2) → Prop (l1 ⊔ l3 ⊔ l4)
  preserves-operations-Algebra-Prop f =
    ( preserves-operations-Algebra f) , (is-prop-preserves-operations-Algebra f)

  hom-Algebra : UU (l1 ⊔ l3 ⊔ l4)
  hom-Algebra =
    Σ ( type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2)
      ( preserves-operations-Algebra)

  map-hom-Algebra :
    hom-Algebra →
    type-Algebra Sg Th Alg1 →
    type-Algebra Sg Th Alg2
  map-hom-Algebra = pr1

  preserves-operations-hom-Algebra :
    ( f : hom-Algebra) →
    preserves-operations-Algebra (map-hom-Algebra f)
  preserves-operations-hom-Algebra = pr2

  hom-Algebra-Subtype :
    subtype (l1 ⊔ l3 ⊔ l4) (type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2)
  hom-Algebra-Subtype = preserves-operations-Algebra-Prop
```

### Composition of algebra homomorphisms

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 l5 : Level}
  ( Alg1 : Algebra Sg Th l3)
  ( Alg2 : Algebra Sg Th l4)
  ( Alg3 : Algebra Sg Th l5)
  where

  comp-hom-Algebra :
    (g : hom-Algebra Sg Th Alg2 Alg3) (f : hom-Algebra Sg Th Alg1 Alg2) →
    hom-Algebra Sg Th Alg1 Alg3
  pr1 (comp-hom-Algebra (g , _) (f , _)) = g ∘ f
  pr2 (comp-hom-Algebra (g , q) (f , p)) op v =
    equational-reasoning
    pr1 (comp-hom-Algebra (g , q) (f , p)) (pr2 (pr1 Alg1) op v)
    ＝ g (pr2 (pr1 Alg2) op (map-tuple f v))
      by ap g (p op v)
    ＝ pr2 (pr1 Alg3) op (map-tuple g (map-tuple f v))
      by q op (map-tuple f v)
    ＝ pr2 (pr1 Alg3) op
      (map-tuple (pr1 (comp-hom-Algebra (g , q) (f , p))) v)
      by ap (pr2 (pr1 Alg3) op)
      ( preserves-comp-map-tuple
        ( pr1 (pr1 (pr1 Alg1)))
        ( pr1 (pr1 (pr1 Alg2)))
        ( pr1 (pr1 (pr1 Alg3)))
        ( pr2 Sg op)
        v f g)
```

## Properties

### The type of algebra homomorphisms for any theory is a set

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 : Level}
  ( Alg1 : Algebra Sg Th l3)
  ( Alg2 : Algebra Sg Th l4)
  where

  is-set-hom-Algebra : is-set (hom-Algebra Sg Th Alg1 Alg2)
  is-set-hom-Algebra =
    is-set-type-subtype
    ( hom-Algebra-Subtype Sg Th Alg1 Alg2)
    ( is-set-hom-Set (set-Algebra Sg Th Alg1) (set-Algebra Sg Th Alg2))

  set-hom-Algebra : Set (l1 ⊔ l3 ⊔ l4)
  set-hom-Algebra = (hom-Algebra Sg Th Alg1 Alg2) , is-set-hom-Algebra

  htpy-hom-Algebra : (f g : hom-Algebra Sg Th Alg1 Alg2) → UU (l3 ⊔ l4)
  htpy-hom-Algebra (f , _) (g , _) = f ~ g

  htpy-eq-hom-Algebra :
    (f g : hom-Algebra Sg Th Alg1 Alg2) → f ＝ g → htpy-hom-Algebra f g
  htpy-eq-hom-Algebra f .f refl x = refl

  is-equiv-htpy-eq-hom-Algebra :
    (f g : hom-Algebra Sg Th Alg1 Alg2) → is-equiv (htpy-eq-hom-Algebra f g)
  is-equiv-htpy-eq-hom-Algebra (f , p) =
    subtype-identity-principle
    ( is-prop-preserves-operations-Algebra Sg Th Alg1 Alg2)
    ( p)
    ( refl-htpy)
    ( htpy-eq-hom-Algebra (f , p))
    ( funext f)

  equiv-htpy-eq-hom-Algebra :
    (f g : hom-Algebra Sg Th Alg1 Alg2) → (f ＝ g) ≃ (htpy-hom-Algebra f g)
  equiv-htpy-eq-hom-Algebra f g =
    (htpy-eq-hom-Algebra f g) , is-equiv-htpy-eq-hom-Algebra f g

  eq-htpy-hom-Algebra :
    (f g : hom-Algebra Sg Th Alg1 Alg2) → htpy-hom-Algebra f g → f ＝ g
  eq-htpy-hom-Algebra f g = map-inv-equiv (equiv-htpy-eq-hom-Algebra f g)
```

### The identity map is an algebra homomorphism

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 : Level} ( Alg : Algebra Sg Th l3)
  where

  is-hom-id-Algebra : preserves-operations-Algebra Sg Th Alg Alg id
  is-hom-id-Algebra op v =
    ap
    ( pr2 (pr1 Alg) op)
    ( preserves-id-map-tuple (pr1 (pr1 (pr1 Alg))) (pr2 Sg op) v)

  id-hom-Algebra : hom-Algebra Sg Th Alg Alg
  id-hom-Algebra = id , is-hom-id-Algebra
```

### Composition of algebra homomorphisms is associative

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 l5 l6 : Level}
  { Alg1 : Algebra Sg Th l3}
  { Alg2 : Algebra Sg Th l4}
  { Alg3 : Algebra Sg Th l5}
  { Alg4 : Algebra Sg Th l6}
  where

  associative-comp-hom-Algebra :
    (h : hom-Algebra Sg Th Alg3 Alg4)
    (g : hom-Algebra Sg Th Alg2 Alg3)
    (f : hom-Algebra Sg Th Alg1 Alg2) →
    comp-hom-Algebra Sg Th Alg1 Alg2 Alg4
      ( comp-hom-Algebra Sg Th Alg2 Alg3 Alg4 h g) f ＝
    comp-hom-Algebra Sg Th Alg1 Alg3 Alg4 h
      ( comp-hom-Algebra Sg Th Alg1 Alg2 Alg3 g f)
  associative-comp-hom-Algebra h g f =
    eq-htpy-hom-Algebra Sg Th Alg1 Alg4
    ( comp-hom-Algebra Sg Th Alg1 Alg2 Alg4
      ( comp-hom-Algebra Sg Th Alg2 Alg3 Alg4 h g) f)
    ( comp-hom-Algebra Sg Th Alg1 Alg3 Alg4 h
      ( comp-hom-Algebra Sg Th Alg1 Alg2 Alg3 g f))
    ( refl-htpy)
```

### Left and right unit laws for homomorphism composition

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 : Level}
  { Alg1 : Algebra Sg Th l3}
  { Alg2 : Algebra Sg Th l4}
  where

  left-unit-law-comp-hom-Algebra :
    (f : hom-Algebra Sg Th Alg1 Alg2) →
    comp-hom-Algebra Sg Th Alg1 Alg2 Alg2 (id-hom-Algebra Sg Th Alg2) f ＝ f
  left-unit-law-comp-hom-Algebra f =
    eq-htpy-hom-Algebra Sg Th Alg1 Alg2
    ( comp-hom-Algebra Sg Th Alg1 Alg2 Alg2 (id-hom-Algebra Sg Th Alg2) f) f
    ( refl-htpy)

  right-unit-law-comp-hom-Algebra :
    (f : hom-Algebra Sg Th Alg1 Alg2) →
    comp-hom-Algebra Sg Th Alg1 Alg1 Alg2 f (id-hom-Algebra Sg Th Alg1) ＝ f
  right-unit-law-comp-hom-Algebra f =
    eq-htpy-hom-Algebra Sg Th Alg1 Alg2
    ( comp-hom-Algebra Sg Th Alg1 Alg1 Alg2 f (id-hom-Algebra Sg Th Alg1)) f
    ( refl-htpy)
```
