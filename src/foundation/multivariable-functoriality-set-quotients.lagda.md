# Multivariable functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.multivariable-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.functoriality-set-quotients
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.equivalence-classes
open import foundation.identity-types
open import foundation.multivariable-operations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.reflecting-maps-equivalence-relations
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.small-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.subtype-identity-principle

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`, as well as a type `X` equipped with an equivalence relation `X`,
Then, any multivariable operation from the `Ai`s to the `X` that respects the
equivalence relations extends uniquely to a multivariable operation from the
`Ai/Ri`s to `X/S`.

## Definition

### n-ary hom of equivalence relation

```agda
all-sim-Rel :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  ( as a's : multivariable-input n As) →
  UU l2
all-sim-Rel {l1} {l2} zero-ℕ As Rs as a's =
  raise-unit l2
all-sim-Rel {l1} {l2} (succ-ℕ n) As Rs as a's =
  sim-Eq-Rel (Rs (inr star))
    ( head-multivariable-input n As as)
    ( head-multivariable-input n As a's) ×
  all-sim-Rel n
    ( tail-functional-vec n As)
    ( λ i → Rs (inl-Fin n i))
    ( tail-multivariable-input n As as)
    ( tail-multivariable-input n As a's)

is-prop-all-sim-Rel :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  ( as : multivariable-input n As) →
  ( a's : multivariable-input n As) →
  is-prop (all-sim-Rel n As Rs as a's)
is-prop-all-sim-Rel zero-ℕ As Rs as a's =
  is-prop-raise-unit 
is-prop-all-sim-Rel (succ-ℕ n) As Rs as a's =
  is-prop-prod
    ( is-prop-sim-Eq-Rel (Rs (neg-one-Fin n)) _ _)
    ( is-prop-all-sim-Rel n
      ( tail-functional-vec n As)
      ( λ i → Rs (inl i))
      ( tail-multivariable-input n As as)
      ( tail-multivariable-input n As a's))

all-sim-Rel-Prop :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  ( Rel-Prop l2 (multivariable-input n As))
all-sim-Rel-Prop n As Rs as a's =
  pair
   (all-sim-Rel n As Rs as a's)
   (is-prop-all-sim-Rel n As Rs as a's)

is-reflexive-all-sim-Rel-Prop :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  is-reflexive-Rel-Prop (all-sim-Rel-Prop n As Rs)
is-reflexive-all-sim-Rel-Prop zero-ℕ As Rs = raise-star
is-reflexive-all-sim-Rel-Prop (succ-ℕ n) As Rs =
  pair
    ( refl-Eq-Rel (Rs (neg-one-Fin n)))
    ( is-reflexive-all-sim-Rel-Prop n
      ( tail-functional-vec n As)
      ( λ i → Rs (inl i)))

is-symmetric-all-sim-Rel-Prop :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  is-symmetric-Rel-Prop (all-sim-Rel-Prop n As Rs)
is-symmetric-all-sim-Rel-Prop zero-ℕ As Rs p = raise-star
is-symmetric-all-sim-Rel-Prop (succ-ℕ n) As Rs (p , p') =
  pair
    (symm-Eq-Rel (Rs (neg-one-Fin n)) p)
    (is-symmetric-all-sim-Rel-Prop n
      ( tail-functional-vec n As)
      ( λ i → Rs (inl i))
      ( p'))

is-transitive-all-sim-Rel-Prop :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  is-transitive-Rel-Prop (all-sim-Rel-Prop n As Rs)
is-transitive-all-sim-Rel-Prop zero-ℕ As Rs p q = raise-star
is-transitive-all-sim-Rel-Prop (succ-ℕ n) As Rs (p , p') (q , q') =
  pair
    ( trans-Eq-Rel (Rs (neg-one-Fin n)) p q)
    ( is-transitive-all-sim-Rel-Prop n
      ( tail-functional-vec n As)
      ( λ i → Rs (inl i))
      ( p')
      ( q'))

all-sim-Eq-Rel :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  ( Eq-Rel l2 (multivariable-input n As))
all-sim-Eq-Rel {l1} {l2} n As Rs =
  pair
   ( all-sim-Rel-Prop n As Rs)
   ( pair
     ( is-reflexive-all-sim-Rel-Prop n As Rs)
     ( pair
       ( is-symmetric-all-sim-Rel-Prop n As Rs)
       ( is-transitive-all-sim-Rel-Prop n As Rs)))

module _
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i))
  ( X : UU l1) (S : Eq-Rel l2 X)
  where

  preserves-sim-multivariable-map-Eq-Rel :
    multivariable-operation n As X →
    UU (l1 ⊔ l2)
  preserves-sim-multivariable-map-Eq-Rel f =
    ( as : multivariable-input n As) →
    ( a's : multivariable-input n As) →
    ( all-sim-Rel n As Rs as a's) →
    ( sim-Eq-Rel S
      ( f as)
      ( f a's))

  is-prop-preserves-sim-n-ary-map-Eq-Rel :
    (f : multivariable-operation n As X) →
    is-prop (preserves-sim-multivariable-map-Eq-Rel f)
  is-prop-preserves-sim-n-ary-map-Eq-Rel f =
    is-prop-Π
      ( λ as →
        ( is-prop-Π
          ( λ a's →
            ( is-prop-Π
              ( λ _ →
                ( is-prop-sim-Eq-Rel S
                  ( f as)
                  ( f a's)))))))

  preserves-sim-multivariable-map-Eq-Rel-Prop :
    multivariable-operation n As X →
    Prop (l1 ⊔ l2)
  preserves-sim-multivariable-map-Eq-Rel-Prop f =
    pair
      ( preserves-sim-multivariable-map-Eq-Rel f)
      ( is-prop-preserves-sim-n-ary-map-Eq-Rel f)

  multivariable-hom-Eq-Rel : UU (l1 ⊔ l2)
  multivariable-hom-Eq-Rel =
    type-subtype preserves-sim-multivariable-map-Eq-Rel-Prop

  map-multivariable-hom-Eq-Rel :
    multivariable-hom-Eq-Rel → multivariable-operation n As X
  map-multivariable-hom-Eq-Rel = pr1

  preserves-sim-multivariable-hom-Eq-Rel :
    ( f : multivariable-hom-Eq-Rel) →
    preserves-sim-multivariable-map-Eq-Rel
     ( map-multivariable-hom-Eq-Rel f)
  preserves-sim-multivariable-hom-Eq-Rel = pr2
```

## Properties

### Characterization of equality of `multivariable-hom-Eq-Rel`

```agda
  multivariable-htpy-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) → UU l1
  multivariable-htpy-hom-Eq-Rel f g =
    ( map-multivariable-hom-Eq-Rel f) ~
      ( map-multivariable-hom-Eq-Rel g)

  refl-multivariable-htpy-hom-Eq-Rel :
    (f : multivariable-hom-Eq-Rel) → multivariable-htpy-hom-Eq-Rel f f
  refl-multivariable-htpy-hom-Eq-Rel f = refl-htpy

  multivariable-htpy-eq-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) → (f ＝ g) →
    multivariable-htpy-hom-Eq-Rel f g
  multivariable-htpy-eq-hom-Eq-Rel f .f refl =
    refl-multivariable-htpy-hom-Eq-Rel f

  is-contr-total-multivariable-htpy-hom-Eq-Rel :
    (f : multivariable-hom-Eq-Rel) →
    is-contr (Σ multivariable-hom-Eq-Rel (multivariable-htpy-hom-Eq-Rel f))
  is-contr-total-multivariable-htpy-hom-Eq-Rel f =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (map-multivariable-hom-Eq-Rel f))
      ( is-prop-preserves-sim-n-ary-map-Eq-Rel)
      ( map-multivariable-hom-Eq-Rel f)
      ( refl-multivariable-htpy-hom-Eq-Rel f)
      ( preserves-sim-multivariable-hom-Eq-Rel f)

  is-equiv-multivariable-htpy-eq-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) →
      is-equiv (multivariable-htpy-eq-hom-Eq-Rel f g)
  is-equiv-multivariable-htpy-eq-hom-Eq-Rel f =
    fundamental-theorem-id
      ( is-contr-total-multivariable-htpy-hom-Eq-Rel f)
      ( multivariable-htpy-eq-hom-Eq-Rel f)

  extensionality-multivariable-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) →
    (f ＝ g) ≃ multivariable-htpy-hom-Eq-Rel f g
  pr1 (extensionality-multivariable-hom-Eq-Rel f g) =
    multivariable-htpy-eq-hom-Eq-Rel f g
  pr2 (extensionality-multivariable-hom-Eq-Rel f g) =
    is-equiv-multivariable-htpy-eq-hom-Eq-Rel f g

  eq-multivariable-htpy-hom-Eq-Rel :
    (f g : multivariable-hom-Eq-Rel) →
    multivariable-htpy-hom-Eq-Rel f g → f ＝ g
  eq-multivariable-htpy-hom-Eq-Rel f g =
    map-inv-equiv (extensionality-multivariable-hom-Eq-Rel f g)
```

### The type `multivariable-hom-Eq-Rel R S T` is equivalent to the type `hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T)`

```agda
module _
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) (succ-ℕ n))
  ( Rs : (i : Fin (succ-ℕ n)) → Eq-Rel l2 (As i))
  ( X : UU l1) (S : Eq-Rel l2 X)
  where

  -- map-hom-multivariable-hom-Eq-Rel :
  --   multivariable-hom-Eq-Rel n As Rs X →
  --   ( tail-functional-vec n As)A → hom-Eq-Rel S T
  -- map-hom-multivariable-hom-Eq-Rel = _
  -- pr1 (map-hom-multivariable-hom-Eq-Rel f a) = map-multivariable-hom-Eq-Rel R S T f a
  -- pr2 (map-hom-multivariable-hom-Eq-Rel f a) {x} {y} s =
  --   preserves-sim-multivariable-hom-Eq-Rel R S T f (refl-Eq-Rel R) s

  equiv-hom-multivariable-hom-Eq-Rel :
    multivariable-hom-Eq-Rel (succ-ℕ n) As Rs X S ≃
      hom-Eq-Rel (Rs (neg-one-Fin n))
        {!!}
    --    {! (multivariable-hom-Eq-Rel n
    -- ( tail-functional-vec n As)
    -- ( λ i → Rs (inl-Fin n i)) X S ) !}
  equiv-hom-multivariable-hom-Eq-Rel = _

is-set-qARs :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  is-set ((i : Fin n) → set-quotient (Rs i))
is-set-qARs n As Rs = is-set-Π (λ i → (is-set-set-quotient (Rs i)))

idk :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  reflecting-map-Eq-Rel (all-sim-Eq-Rel n As Rs) ((i : Fin n) → set-quotient (Rs i))
idk zero-ℕ As Rs = pair (λ _ ()) (λ _  → refl)
idk (succ-ℕ n) As Rs =
  pair (λ as i → quotient-map (Rs i) (as i))
    λ (p , p') → eq-htpy λ i → {!apply-effectiveness-quotient-map' (Rs i) !}
  -- set-quotient (all-sim-Eq-Rel n As Rs) →
  -- ((i : Fin n) → set-quotient (Rs i))


test :
  { l1 l2 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  set-quotient (all-sim-Eq-Rel n As Rs) →
  ((i : Fin n) → set-quotient (Rs i))
test zero-ℕ As Rs qAs ()
test (succ-ℕ n) As Rs qAs =
  cons-multivariable-input' n (λ z → set-quotient (Rs z))
    qa (test n
      ( tail-functional-vec n As)
      (  λ i → Rs (inl i))
      qas    )
  where
    qa : set-quotient (Rs (inr star))
    qa = {!!}
    qas : set-quotient
      (all-sim-Eq-Rel n (tail-functional-vec n As) (λ i → Rs (inl i)))
    qas = {!!}


      -- ( tail-functional-vec n As)
      -- ( λ i → Rs (inl i))
      -- ( tail-multivariable-input n As as)


module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  set-quotient' : small-type-Small-Type (equivalence-class-Small-Type R) ＝
    pr1 (is-small-equivalence-class R)
  set-quotient' = refl
