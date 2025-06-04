# Generated equivalence relations

```agda
module foundation.generated-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Given an arbitrary relation `R`, we construct an equivalence relation using `R`.
First, we construct a new reflexive, symmetric, and transitive relation using
paths of arbitrary length composed of edges of `R`: an edge from `x` to `y` is a
term `R x y + R y x`, i.e. a relation in either direction. A path of length 0 is
an identification `x ＝ y` and a path of length `n+1` is a choice of
intermediate `x'`, a path from `x` to `x'` of length `n`, and an edge from `x'`
to `y`. To construct the resulting equivalence relation we take the
propositional truncation of this path relation.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  edge-Relation : (x y : A) → UU l2
  edge-Relation x y = (R x y) + (R y x)

  inv-edge-Relation : (x y : A) (e : edge-Relation x y) → edge-Relation y x
  inv-edge-Relation x y (inl e) = inr e
  inv-edge-Relation x y (inr e) = inl e

  n-path-Relation : (x y : A) (n : ℕ) → UU (l1 ⊔ l2)
  n-path-Relation x y zero-ℕ = raise l2 (x ＝ y)
  n-path-Relation x y (succ-ℕ n) =
    Σ ( A)
      ( λ x' → (n-path-Relation x x' n) × (edge-Relation x' y))

  n-path-edge-Relation :
    (x y : A) (e : edge-Relation x y) → n-path-Relation x y 1
  n-path-edge-Relation x y e = x , (map-raise refl , e)

  refl-n-path-Relation : (x : A) → n-path-Relation x x zero-ℕ
  refl-n-path-Relation x = map-raise refl

  concat-n-path-Relation : (x y z : A) (n m : ℕ)
    (q : n-path-Relation y z m) (p : n-path-Relation x y n) →
    n-path-Relation x z (n +ℕ m)
  concat-n-path-Relation x y z n zero-ℕ (map-raise q) p = tr _ q p
  concat-n-path-Relation x y z n (succ-ℕ m) (y' , q , e) p =
    ( y') ,
    ( concat-n-path-Relation x y y' n m q p) , e

  inv-n-path-Relation : (x y : A) (n : ℕ)
    (p : n-path-Relation x y n) →
    n-path-Relation y x n
  inv-n-path-Relation x y zero-ℕ (map-raise p) = map-raise (inv p)
  inv-n-path-Relation x y (succ-ℕ n) (x' , p , e) =
    tr (λ m → n-path-Relation y x m) (left-one-law-add-ℕ n)
      ( concat-n-path-Relation y x' x 1 n
        ( inv-n-path-Relation x x' n p)
        ( n-path-edge-Relation y x' (inv-edge-Relation x' y e)))

  path-Relation : Relation (l1 ⊔ l2) A
  path-Relation x y = Σ ℕ (λ n → n-path-Relation x y n)

  is-reflexive-path-Relation : is-reflexive path-Relation
  is-reflexive-path-Relation x = (0 , refl-n-path-Relation x)

  is-symmetric-path-Relation : is-symmetric path-Relation
  is-symmetric-path-Relation x y (n , p) = n , (inv-n-path-Relation x y n p)

  is-transitive-path-Relation : is-transitive path-Relation
  is-transitive-path-Relation x y z (n , q) (m , p) =
    m +ℕ n , concat-n-path-Relation x y z m n q p

  path-Relation-Prop : Relation-Prop (l1 ⊔ l2) A
  path-Relation-Prop x y = trunc-Prop (path-Relation x y)

  is-reflexive-path-Relation-Prop :
    is-reflexive-Relation-Prop path-Relation-Prop
  is-reflexive-path-Relation-Prop =
    unit-trunc-Prop ∘ is-reflexive-path-Relation

  is-symmetric-path-Relation-Prop :
    is-symmetric-Relation-Prop path-Relation-Prop
  is-symmetric-path-Relation-Prop x y =
    rec-trunc-Prop
      ( path-Relation-Prop y x)
      ( unit-trunc-Prop ∘ (is-symmetric-path-Relation x y))
  is-transitive-path-Relation-Prop :
    is-transitive-Relation-Prop path-Relation-Prop
  is-transitive-path-Relation-Prop x y z =
    rec-trunc-Prop
      ( path-Relation-Prop x y ⇒ path-Relation-Prop x z)
      ( λ q →
        rec-trunc-Prop
          ( path-Relation-Prop x z)
          ( λ p → unit-trunc-Prop (is-transitive-path-Relation x y z q p)))

  is-equivalence-relation-path-Relation-Prop :
    is-equivalence-relation path-Relation-Prop
  is-equivalence-relation-path-Relation-Prop =
    ( is-reflexive-path-Relation-Prop) ,
    ( ( is-symmetric-path-Relation-Prop ,
        is-transitive-path-Relation-Prop))

  equivalence-relation-path-Relation-Prop : equivalence-relation (l1 ⊔ l2) A
  equivalence-relation-path-Relation-Prop =
    path-Relation-Prop , is-equivalence-relation-path-Relation-Prop
```

## Properties

### It suffices to check generators

To show that a function `A → B` reflects this path relation, it suffices to show
this on generators. To show that a function reflects the (propositionally
truncated) equivalence relation, we need also the codomain `B` to be a set.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  reflects-path-Relation :
    {l3 : Level} (B : UU l3) (f : A → B)
    (r : (x y : A) → R x y → f x ＝ f y)
    (x y : A) →
    path-Relation R x y → f x ＝ f y
  reflects-path-Relation B f r x y (zero-ℕ , map-raise refl) = refl
  reflects-path-Relation B f r x y (succ-ℕ n , x' , p , e) =
    ( reflects-path-Relation B f r x x' (n , p)) ∙
    ( forward-r x' y e) where

    forward-r : (a b : A) → edge-Relation R a b → f a ＝ f b
    forward-r a b (inl e) = r a b e
    forward-r a b (inr e) = inv (r b a e)

  reflects-path-Relation-Prop :
    {l3 : Level} (B : Set l3) (f : A → type-Set B)
    (r : (x y : A) → R x y → f x ＝ f y) →
    reflects-equivalence-relation (equivalence-relation-path-Relation-Prop R) f
  reflects-path-Relation-Prop B f r {x} {y} =
    rec-trunc-Prop
      ( Id-Prop B (f x) (f y))
      ( reflects-path-Relation (type-Set B) f r x y)
```
