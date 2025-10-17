# Transpositions

```agda
module finite-group-theory.transpositions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**Transpositions** are [permutations](finite-group-theory.permutations.md) that
swap two elements.

## Definitions

### Transpositions

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where

  map-transposition'' :
    Σ X (λ x → is-decidable (is-in-2-Element-Decidable-Subtype P x)) →
    Σ X (λ x → is-decidable (is-in-2-Element-Decidable-Subtype P x))
  pr1 (map-transposition'' (pair x (inl p))) =
    pr1 (map-swap-2-Element-Decidable-Subtype P (pair x p))
  pr2 (map-transposition'' (pair x (inl p))) =
    inl (pr2 (map-swap-2-Element-Decidable-Subtype P (pair x p)))
  pr1 (map-transposition'' (pair x (inr np))) = x
  pr2 (map-transposition'' (pair x (inr np))) = inr np

  map-transposition' :
    (x : X) (d : is-decidable (is-in-2-Element-Decidable-Subtype P x)) → X
  map-transposition' x (inl p) =
    pr1 (map-swap-2-Element-Decidable-Subtype P (pair x p))
  map-transposition' x (inr np) = x

  map-transposition : X → X
  map-transposition x =
    map-transposition' x
      ( is-decidable-subtype-subtype-2-Element-Decidable-Subtype P x)

  preserves-subtype-map-transposition :
    (x : X) → is-in-2-Element-Decidable-Subtype P x →
    is-in-2-Element-Decidable-Subtype P (map-transposition x)
  preserves-subtype-map-transposition x p =
    tr
      ( λ R → is-in-2-Element-Decidable-Subtype P (map-transposition' x R))
      { x = inl p}
      { y = is-decidable-subtype-subtype-2-Element-Decidable-Subtype P x}
      ( eq-is-prop
        ( is-prop-is-decidable
          ( is-prop-is-in-2-Element-Decidable-Subtype P x)))
      ( pr2
        ( map-swap-2-Element-Type
          ( 2-element-type-2-Element-Decidable-Subtype P)
          ( pair x p)))

  is-involution-map-transposition' :
    (x : X) (d : is-decidable (is-in-2-Element-Decidable-Subtype P x))
    (d' : is-decidable
          ( is-in-2-Element-Decidable-Subtype P (map-transposition' x d))) →
    map-transposition' (map-transposition' x d) d' ＝ x
  is-involution-map-transposition' x (inl p) (inl p') =
    ( ap
      ( λ y → map-transposition' (map-transposition' x (inl p)) (inl y))
      ( eq-is-in-2-Element-Decidable-Subtype P)) ∙
    ( ap
      ( pr1)
      ( is-involution-aut-2-element-type
        ( 2-element-type-2-Element-Decidable-Subtype P)
        ( swap-2-Element-Decidable-Subtype P)
        ( pair x p)))
  is-involution-map-transposition' x (inl p) (inr np') =
    ex-falso (np' (pr2 (map-swap-2-Element-Decidable-Subtype P (pair x p))))
  is-involution-map-transposition' x (inr np) (inl p') = ex-falso (np p')
  is-involution-map-transposition' x (inr np) (inr np') = refl

  is-involution-map-transposition : is-involution map-transposition
  is-involution-map-transposition x =
    is-involution-map-transposition' x
      ( is-decidable-subtype-subtype-2-Element-Decidable-Subtype P x)
      ( is-decidable-subtype-subtype-2-Element-Decidable-Subtype P
        ( map-transposition' x
          ( is-decidable-subtype-subtype-2-Element-Decidable-Subtype P x)))

  is-equiv-map-transposition : is-equiv map-transposition
  is-equiv-map-transposition =
    is-equiv-is-involution is-involution-map-transposition

  transposition : X ≃ X
  pr1 transposition = map-transposition
  pr2 transposition = is-equiv-map-transposition

module _
  {l1 l2 : Level} {X : UU l1}
  where

  is-transposition-permutation-Prop : X ≃ X → Prop (l1 ⊔ lsuc l2)
  is-transposition-permutation-Prop f =
    trunc-Prop (fiber (transposition {l2 = l2}) f)

  is-transposition-permutation : X ≃ X → UU (l1 ⊔ lsuc l2)
  is-transposition-permutation f =
    type-Prop (is-transposition-permutation-Prop f)

  is-prop-is-transposition-permutation :
    (f : X ≃ X) → is-prop (is-transposition-permutation f)
  is-prop-is-transposition-permutation f =
    is-prop-type-Prop (is-transposition-permutation-Prop f)
```

### The standard transposition obtained from a pair of distinct points

```agda
module _
  {l : Level} {X : UU l} (H : has-decidable-equality X)
  {x y : X} (p : x ≠ y)
  where

  standard-transposition : Aut X
  standard-transposition =
    transposition (standard-2-Element-Decidable-Subtype H p)

  map-standard-transposition : X → X
  map-standard-transposition = map-equiv standard-transposition

  abstract
    left-computation-standard-transposition :
      map-standard-transposition x ＝ y
    left-computation-standard-transposition
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtype H p x
    ... | inl pp =
      ap
        pr1
        ( compute-swap-2-Element-Type
          ( 2-element-type-standard-2-Element-Decidable-Subtype H p)
          ( pair x pp)
          ( pair y (inr refl))
          ( λ q → p (ap pr1 q)))
    ... | inr np = ex-falso (np (inl refl))

  abstract
    right-computation-standard-transposition :
      map-standard-transposition y ＝ x
    right-computation-standard-transposition
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtype H p y
    ... | inl pp =
      ap
        pr1
        ( compute-swap-2-Element-Type
          ( 2-element-type-standard-2-Element-Decidable-Subtype H p)
          ( pair y pp)
          ( pair x (inl refl))
          ( λ q → p (ap pr1 (inv q))))
    ... | inr np = ex-falso (np (inr refl))

  abstract
    is-fixed-point-standard-transposition :
      (z : X) → x ≠ z → y ≠ z →
      map-standard-transposition z ＝ z
    is-fixed-point-standard-transposition z q r
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtype H p z
    ... | inl (inl h) = ex-falso (q h)
    ... | inl (inr h) = ex-falso (r h)
    ... | inr np = refl
```

### The permutation obtained from a list of transpositions

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  permutation-list-transpositions :
    ( list (2-Element-Decidable-Subtype l2 X)) → Aut X
  permutation-list-transpositions =
    fold-list id-equiv (λ P e → (transposition P) ∘e e)

  -- !! Why not a homotopy?
  eq-concat-permutation-list-transpositions :
    (l l' : list (2-Element-Decidable-Subtype l2 X)) →
    ( permutation-list-transpositions l) ∘e
    ( permutation-list-transpositions l') ＝
    ( permutation-list-transpositions (concat-list l l'))
  eq-concat-permutation-list-transpositions nil l' = eq-htpy-equiv refl-htpy
  eq-concat-permutation-list-transpositions (cons P l) l' =
    eq-htpy-equiv
      ( λ x →
        ap
          ( map-equiv (transposition P))
          ( htpy-eq-equiv (eq-concat-permutation-list-transpositions l l') x))
```

## Properties

### A transposition is not the identity equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where

  abstract
    is-not-identity-map-transposition : map-transposition P ＝ id → empty
    is-not-identity-map-transposition f =
      is-not-identity-swap-2-Element-Type
        ( 2-element-type-2-Element-Decidable-Subtype P)
        ( eq-htpy-equiv
          ( λ (x , p) →
            eq-pair-Σ
              ( ( ap
                  ( map-transposition' P x)
                  ( eq-is-prop
                    ( is-prop-is-decidable
                      ( is-prop-is-in-2-Element-Decidable-Subtype P x))
                      { y =
                        is-decidable-subtype-subtype-2-Element-Decidable-Subtype
                          ( P)
                          ( x)})) ∙
                ( htpy-eq f x))
              ( eq-is-in-2-Element-Decidable-Subtype P)))
```

### Any transposition on a type equipped with a counting is a standard transposition

```agda
module _
  {l : Level} {X : UU l} (eX : count X)
  (Y : 2-Element-Decidable-Subtype l X)
  where

  element-is-not-identity-map-transposition :
    Σ X (λ x → map-transposition Y x ≠ x)
  element-is-not-identity-map-transposition =
    exists-not-not-for-all-count
      ( λ z → map-transposition Y z ＝ z)
      ( λ x → has-decidable-equality-count eX (map-transposition Y x) x)
      ( eX)
      ( λ H → is-not-identity-map-transposition Y (eq-htpy H))

  two-elements-transposition :
    Σ ( X)
      ( λ x →
        Σ ( X)
          ( λ y →
            Σ ( x ≠ y)
              ( λ np →
                Id
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-count eX)
                    ( np))
                  ( Y))))
  pr1 two-elements-transposition =
    pr1 element-is-not-identity-map-transposition
  pr1 (pr2 two-elements-transposition) =
    map-transposition Y (pr1 element-is-not-identity-map-transposition)
  pr1 (pr2 (pr2 two-elements-transposition)) p =
    pr2 element-is-not-identity-map-transposition (inv p)
  pr2 (pr2 (pr2 two-elements-transposition)) =
    eq-pair-Σ
      ( eq-htpy
        ( λ x → eq-pair-Σ
          ( ap pr1
            { x =
              subtype-standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( pr1 (pr2 (pr2 two-elements-transposition)))
              ( x)}
            { y = subtype-2-Element-Decidable-Subtype Y x}
            ( eq-iff
              (type-t-coproduct-id x)
              (coproduct-id-type-t x)))
          ( eq-pair-Σ
            ( eq-is-prop (is-prop-is-prop (pr1 (pr1 Y x))))
            ( eq-is-prop (is-prop-is-decidable (pr1 (pr2 (pr1 Y x))))))))
      ( eq-is-prop
        ( pr2
          ( has-cardinality-ℕ-Prop 2
            ( Σ X (λ x → type-Decidable-Prop (pr1 Y x))))))
    where
    type-decidable-prop-pr1-two-elements-transposition :
      is-in-2-Element-Decidable-Subtype Y (pr1 two-elements-transposition)
    type-decidable-prop-pr1-two-elements-transposition =
      cases-type-decidable-prop-pr1-two-elements-transposition
        ( is-decidable-subtype-subtype-2-Element-Decidable-Subtype Y
          ( pr1 two-elements-transposition))
      where
      cases-type-decidable-prop-pr1-two-elements-transposition :
        is-decidable
          ( is-in-2-Element-Decidable-Subtype Y
            ( pr1 two-elements-transposition)) →
        is-in-2-Element-Decidable-Subtype Y (pr1 two-elements-transposition)
      cases-type-decidable-prop-pr1-two-elements-transposition (inl Q) = Q
      cases-type-decidable-prop-pr1-two-elements-transposition (inr NQ) =
        ex-falso
          ( pr2 element-is-not-identity-map-transposition
            ( ap
              ( λ R →
                map-transposition' Y (pr1 (two-elements-transposition)) R)
            { x =
              is-decidable-subtype-subtype-2-Element-Decidable-Subtype Y
                ( pr1 two-elements-transposition)}
            { y = inr NQ}
            ( eq-is-prop
              ( is-prop-is-decidable
                ( is-prop-is-in-2-Element-Decidable-Subtype Y
                  ( pr1 two-elements-transposition))))))
    type-decidable-prop-pr1-pr2-two-elements-transposition :
      is-in-2-Element-Decidable-Subtype Y (pr1 (pr2 two-elements-transposition))
    type-decidable-prop-pr1-pr2-two-elements-transposition =
      preserves-subtype-map-transposition Y (pr1 two-elements-transposition)
        ( type-decidable-prop-pr1-two-elements-transposition)
    type-t-coproduct-id :
      (x : X) →
      ( pr1 two-elements-transposition ＝ x) +
      ( pr1 (pr2 two-elements-transposition) ＝ x) →
      type-Decidable-Prop (pr1 Y x)
    type-t-coproduct-id x (inl Q) =
      tr
        ( is-in-2-Element-Decidable-Subtype Y)
        ( Q)
        ( type-decidable-prop-pr1-two-elements-transposition)
    type-t-coproduct-id x (inr Q) =
      tr
        ( is-in-2-Element-Decidable-Subtype Y)
        ( Q)
        ( type-decidable-prop-pr1-pr2-two-elements-transposition)
    cases-coproduct-id-type-t :
      (x : X) (p : is-in-2-Element-Decidable-Subtype Y x) →
      (h : Fin 2 ≃ type-2-Element-Decidable-Subtype Y) →
      (k1 k2 k3 : Fin 2) →
      map-inv-equiv h (pair x p) ＝ k1 →
      Id
        ( map-inv-equiv h
          ( pair
            ( pr1 two-elements-transposition)
            ( type-decidable-prop-pr1-two-elements-transposition)))
        ( k2) →
      Id
        ( map-inv-equiv h
          ( pair
            ( pr1 (pr2 two-elements-transposition))
            ( type-decidable-prop-pr1-pr2-two-elements-transposition)))
        ( k3) →
      ( pr1 two-elements-transposition ＝ x) +
      ( pr1 (pr2 two-elements-transposition) ＝ x)
    cases-coproduct-id-type-t
      x p h (inl (inr star)) (inl (inr star)) k3 K1 K2 K3 =
      inl (ap pr1 (is-injective-equiv (inv-equiv h) (K2 ∙ inv K1)))
    cases-coproduct-id-type-t x p h
      (inl (inr star)) (inr star) (inl (inr star)) K1 K2 K3 =
      inr (ap pr1 (is-injective-equiv (inv-equiv h) (K3 ∙ inv K1)))
    cases-coproduct-id-type-t x p h
      (inl (inr star)) (inr star) (inr star) K1 K2 K3 =
      ex-falso
        ( pr2 element-is-not-identity-map-transposition
        ( inv
          ( ap pr1
            ( is-injective-equiv (inv-equiv h) (K2 ∙ inv K3)))))
    cases-coproduct-id-type-t x p h
      (inr star) (inl (inr star)) (inl (inr star)) K1 K2 K3 =
      ex-falso
        ( pr2 element-is-not-identity-map-transposition
        ( inv
          ( ap pr1
            ( is-injective-equiv (inv-equiv h) (K2 ∙ inv K3)))))
    cases-coproduct-id-type-t x p h
      (inr star) (inl (inr star)) (inr star) K1 K2 K3 =
      inr (ap pr1 (is-injective-equiv (inv-equiv h) (K3 ∙ inv K1)))
    cases-coproduct-id-type-t x p h (inr star) (inr star) k3 K1 K2 K3 =
      inl (ap pr1 (is-injective-equiv (inv-equiv h) (K2 ∙ inv K1)))
    coproduct-id-type-t :
      (x : X) → type-Decidable-Prop (pr1 Y x) →
      ( pr1 two-elements-transposition ＝ x) +
      ( pr1 (pr2 two-elements-transposition) ＝ x)
    coproduct-id-type-t x p =
      apply-universal-property-trunc-Prop (pr2 Y)
        ( coproduct-Prop
          ( Id-Prop
            ( pair X (is-set-count eX))
            ( pr1 two-elements-transposition)
            ( x))
          ( Id-Prop
            ( pair X (is-set-count eX))
            ( pr1 (pr2 two-elements-transposition))
            ( x))
          ( λ q r →
            pr2 element-is-not-identity-map-transposition (inv (q ∙ inv r))))
        ( λ h →
          cases-coproduct-id-type-t x p h
            ( map-inv-equiv h (pair x p))
            ( map-inv-equiv h
              ( pair
                ( pr1 two-elements-transposition)
                ( type-decidable-prop-pr1-two-elements-transposition)))
            ( map-inv-equiv h
              ( pair
                ( pr1 (pr2 two-elements-transposition))
                ( type-decidable-prop-pr1-pr2-two-elements-transposition)))
            ( refl)
            ( refl)
            ( refl))

  element-two-elements-transposition : X
  element-two-elements-transposition =
    pr1 (two-elements-transposition)

  other-element-two-elements-transposition : X
  other-element-two-elements-transposition =
    pr1 (pr2 two-elements-transposition)

  neq-elements-two-elements-transposition :
    element-two-elements-transposition ≠
    other-element-two-elements-transposition
  neq-elements-two-elements-transposition =
    pr1 (pr2 (pr2 two-elements-transposition))

  abstract
    cases-eq-two-elements-transposition :
      (x y : X) (np : x ≠ y) →
      type-Decidable-Prop (pr1 Y x) →
      type-Decidable-Prop (pr1 Y y) →
      is-decidable (pr1 two-elements-transposition ＝ x) →
      is-decidable (pr1 (pr2 two-elements-transposition) ＝ x) →
      is-decidable (pr1 two-elements-transposition ＝ y) →
      is-decidable (pr1 (pr2 two-elements-transposition) ＝ y) →
      ( ( pr1 two-elements-transposition ＝ x) ×
        ( pr1 (pr2 two-elements-transposition) ＝ y)) +
      ( ( pr1 two-elements-transposition ＝ y) ×
        ( pr1 (pr2 two-elements-transposition) ＝ x))
    cases-eq-two-elements-transposition x y np p1 p2 (inl q) r s (inl u) =
      inl (pair q u)
    cases-eq-two-elements-transposition x y np p1 p2 (inl q) r s (inr nu) =
      ex-falso
        ( contradiction-3-distinct-element-2-Element-Type
          ( 2-element-type-2-Element-Decidable-Subtype
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( pr1 (pr2 (pr2 two-elements-transposition)))))
          ( pair (pr1 two-elements-transposition) (inl refl))
          ( pair (pr1 (pr2 two-elements-transposition)) (inr refl))
          ( pair
            ( y)
            ( tr
              ( λ Y → type-Decidable-Prop (pr1 Y y))
              ( inv (pr2 (pr2 (pr2 two-elements-transposition))))
              ( p2)))
          ( λ p →
            pr1
              ( pr2 (pr2 two-elements-transposition))
              ( pr1 (pair-eq-Σ p)))
          ( λ p → nu (pr1 (pair-eq-Σ p)))
          ( λ p → np (inv q ∙ pr1 (pair-eq-Σ p))))
    cases-eq-two-elements-transposition
      x y np p1 p2 (inr nq) (inl r) (inl s) u =
      inr (pair s r)
    cases-eq-two-elements-transposition
      x y np p1 p2 (inr nq) (inl r) (inr ns) u =
      ex-falso
        ( contradiction-3-distinct-element-2-Element-Type
          ( 2-element-type-2-Element-Decidable-Subtype
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( pr1 (pr2 (pr2 two-elements-transposition)))))
          ( pair (pr1 two-elements-transposition) (inl refl))
          ( pair (pr1 (pr2 two-elements-transposition)) (inr refl))
          ( pair
            ( y)
            ( tr
              ( λ Y → type-Decidable-Prop (pr1 Y y))
              ( inv (pr2 (pr2 (pr2 two-elements-transposition))))
              ( p2)))
          ( λ p →
            pr1
              ( pr2 (pr2 two-elements-transposition))
              ( pr1 (pair-eq-Σ p)))
          ( λ p → np (inv r ∙ pr1 (pair-eq-Σ p)))
          ( λ p → ns (pr1 (pair-eq-Σ p))))
    cases-eq-two-elements-transposition x y np p1 p2 (inr nq) (inr nr) s u =
      ex-falso
        ( contradiction-3-distinct-element-2-Element-Type
          ( 2-element-type-2-Element-Decidable-Subtype
            ( standard-2-Element-Decidable-Subtype
              ( has-decidable-equality-count eX)
              ( pr1 (pr2 (pr2 two-elements-transposition)))))
          ( pair (pr1 two-elements-transposition) (inl refl))
          ( pair (pr1 (pr2 two-elements-transposition)) (inr refl))
          ( pair
            ( x)
            ( tr
              ( λ Y → type-Decidable-Prop (pr1 Y x))
              ( inv (pr2 (pr2 (pr2 two-elements-transposition))))
              ( p1)))
          ( λ p →
            pr1
              ( pr2 (pr2 two-elements-transposition))
              ( pr1 (pair-eq-Σ p)))
          ( λ p → nr (pr1 (pair-eq-Σ p)))
          ( λ p → nq (pr1 (pair-eq-Σ p))))

    eq-two-elements-transposition :
      (x y : X) (np : x ≠ y) →
      type-Decidable-Prop (pr1 Y x) →
      type-Decidable-Prop (pr1 Y y) →
      ( ( pr1 two-elements-transposition ＝ x) ×
        ( pr1 (pr2 two-elements-transposition) ＝ y)) +
      ( ( pr1 two-elements-transposition ＝ y) ×
        ( pr1 (pr2 two-elements-transposition) ＝ x))
    eq-two-elements-transposition x y np p1 p2 =
      cases-eq-two-elements-transposition x y np p1 p2
        ( has-decidable-equality-count eX (pr1 two-elements-transposition) x)
        ( has-decidable-equality-count
          ( eX)
          ( pr1 (pr2 two-elements-transposition))
          ( x))
        ( has-decidable-equality-count eX (pr1 two-elements-transposition) y)
        ( has-decidable-equality-count
          ( eX)
          ( pr1 (pr2 two-elements-transposition))
          ( y))
```

#### The case of `Fin n`

```agda
module _
  {n : ℕ}
  (Y : 2-Element-Decidable-Subtype (lzero) (Fin n))
  where

  two-elements-transposition-Fin :
    Σ ( Fin n)
      ( λ x →
        Σ ( Fin n)
          ( λ y →
            Σ ( x ≠ y)
              ( λ np →
                Id
                  ( standard-2-Element-Decidable-Subtype
                    ( has-decidable-equality-Fin n)
                    ( np))
                  ( Y))))
  two-elements-transposition-Fin =
    tr
      ( λ p →
        Σ ( Fin n)
          ( λ x →
            Σ ( Fin n)
              ( λ y →
                Σ ( x ≠ y)
                  ( λ np → standard-2-Element-Decidable-Subtype p np ＝ Y))))
      ( eq-is-prop (is-prop-has-decidable-equality))
      ( two-elements-transposition (count-Fin n) Y)

  element-two-elements-transposition-Fin : Fin n
  element-two-elements-transposition-Fin =
    pr1 (two-elements-transposition-Fin)

  other-element-two-elements-transposition-Fin : Fin n
  other-element-two-elements-transposition-Fin =
    pr1 (pr2 two-elements-transposition-Fin)

  neq-elements-two-elements-transposition-Fin :
    element-two-elements-transposition-Fin ≠
    other-element-two-elements-transposition-Fin
  neq-elements-two-elements-transposition-Fin =
    pr1 (pr2 (pr2 two-elements-transposition-Fin))

  eq-standard-2-element-decidable-subtype-two-elements-transposition-Fin :
    standard-2-Element-Decidable-Subtype
      ( has-decidable-equality-Fin n)
      ( neq-elements-two-elements-transposition-Fin) ＝
    Y
  eq-standard-2-element-decidable-subtype-two-elements-transposition-Fin =
    pr2 (pr2 (pr2 two-elements-transposition-Fin))

  htpy-two-elements-transpositon-Fin :
    htpy-equiv
      ( standard-transposition
        ( has-decidable-equality-Fin n)
        ( neq-elements-two-elements-transposition-Fin))
      ( transposition Y)
  htpy-two-elements-transpositon-Fin =
    htpy-eq
      ( ap
        map-transposition
        eq-standard-2-element-decidable-subtype-two-elements-transposition-Fin)
```

### Transpositions can be transported along equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (X : UU l1) (Y : UU l2) (e : X ≃ Y)
  where

  transposition-conjugation-equiv :
    ( Σ
      ( X → Decidable-Prop l3)
      ( λ P →
        has-cardinality-ℕ
          ( 2)
          ( Σ X (type-Decidable-Prop ∘ P)))) →
      ( Σ
        ( Y → Decidable-Prop (l3 ⊔ l4))
        ( λ P →
          has-cardinality-ℕ 2
            ( Σ Y (type-Decidable-Prop ∘ P))))
  pr1 (pr1 (transposition-conjugation-equiv (pair P H)) x) =
    raise l4 (type-Decidable-Prop (P (map-inv-equiv e x)))
  pr1 (pr2 (pr1 (transposition-conjugation-equiv (pair P H)) x)) =
    is-prop-all-elements-equal
      (λ p1 p2 →
        is-injective-equiv
          ( inv-equiv
            ( compute-raise l4 (type-Decidable-Prop (P (map-inv-equiv e x)))))
          ( eq-is-prop (is-prop-type-Decidable-Prop (P (map-inv-equiv e x)))))
  pr2 (pr2 (pr1 (transposition-conjugation-equiv (pair P H)) x)) =
    is-decidable-raise l4
      ( type-Decidable-Prop (P (map-inv-equiv e x)))
      ( is-decidable-Decidable-Prop (P (map-inv-equiv e x)))
  pr2 (transposition-conjugation-equiv (pair P H)) =
    apply-universal-property-trunc-Prop
      ( H)
      ( has-cardinality-ℕ-Prop 2
        ( Σ Y (λ x → raise l4 (type-Decidable-Prop (P (map-inv-equiv e x))))))
      λ h →
      unit-trunc-Prop
        ( pair
          ( λ x →
            pair
              ( map-equiv e (pr1 (map-equiv h x)))
              ( tr
                ( λ g →
                  raise l4
                    ( type-Decidable-Prop
                      ( P (map-equiv g (pr1 (map-equiv h x))))))
                ( inv (left-inverse-law-equiv e))
                ( map-raise (pr2 (map-equiv h x)))))
          ( is-equiv-is-invertible
            ( λ (pair x p) →
              map-inv-equiv h ( pair (map-inv-equiv e x) (map-inv-raise p)))
            ( λ (pair x p) →
              eq-pair-Σ
                ( ( ap
                    ( λ g →
                      map-equiv
                        ( e)
                        ( pr1
                          ( map-equiv
                            ( g)
                            ( pair (map-inv-equiv e x) (map-inv-raise p)))))
                    ( right-inverse-law-equiv h)) ∙
                  ( ap (λ g → map-equiv g x) (right-inverse-law-equiv e)))
                ( eq-is-prop
                  ( pr1
                    ( pr2
                      ( pr1
                        ( transposition-conjugation-equiv (pair P H))
                        ( x))))))
            ( λ b →
              ( ap
                ( λ w →
                  map-inv-equiv
                    ( h)
                    ( pair (map-equiv (pr1 w) (pr1 (map-equiv h b))) (pr2 w)))
                { y = pair id-equiv (pr2 (map-equiv h b))}
                ( eq-pair-Σ
                  ( left-inverse-law-equiv e)
                  ( eq-is-prop
                    ( is-prop-type-Decidable-Prop
                      ( P (pr1 (map-equiv h b)))))) ∙
                ( ap (λ g → map-equiv g b) (left-inverse-law-equiv h))))))

  abstract
    correct-transposition-conjugation-equiv :
      (t : Σ
        ( X → Decidable-Prop l3)
        ( λ P → has-cardinality-ℕ 2 (Σ X (type-Decidable-Prop ∘ P)))) →
      htpy-equiv
        ( transposition
          (transposition-conjugation-equiv t))
        ( (e ∘e (transposition t)) ∘e (inv-equiv e))
    correct-transposition-conjugation-equiv t x =
      cases-correct-transposition-conjugation-equiv
        ( is-decidable-Decidable-Prop (pr1 t (map-inv-equiv e x)))
      where
      cases-correct-transposition-conjugation-equiv :
        (Q : is-decidable (type-Decidable-Prop (pr1 t (map-inv-equiv e x)))) →
        Id
          ( map-transposition'
            (transposition-conjugation-equiv t)
            ( x)
            ( is-decidable-raise
              ( l4)
              ( type-Decidable-Prop (pr1 t (map-inv-equiv e x)))
              ( Q)))
          ( map-equiv e
            ( map-transposition' t (map-inv-equiv e x) Q))
      cases-correct-transposition-conjugation-equiv (inl p) =
        ap
          ( pr1)
          ( compute-swap-2-Element-Type
            ( pair
              ( Σ Y (λ y → pr1 (pr1 (transposition-conjugation-equiv t) y)))
              ( pr2 (transposition-conjugation-equiv t)))
            ( pair x (map-raise p))
            ( pair
              ( map-equiv e (pr1 second-pair-X))
              ( map-raise
                ( tr
                  ( λ g →
                    type-Decidable-Prop
                      ( pr1 t (map-equiv g (pr1 second-pair-X))))
                  ( inv (left-inverse-law-equiv e))
                  ( pr2 second-pair-X))))
            λ q →
              has-no-fixed-points-swap-2-Element-Type
                ( pair (Σ X (λ y → type-Decidable-Prop (pr1 t y))) (pr2 t))
                { pair (map-inv-equiv e x) p}
                ( eq-pair-Σ
                  ( is-injective-equiv
                    ( e)
                    ( inv (pr1 (pair-eq-Σ q)) ∙
                      ap
                        ( λ g → map-equiv g x)
                        ( inv (right-inverse-law-equiv e))))
                  ( eq-is-prop
                    ( is-prop-type-Decidable-Prop
                      ( pr1 t (map-inv-equiv e x))))))
        where
        second-pair-X : Σ X (λ y → type-Decidable-Prop (pr1 t y))
        second-pair-X =
          map-swap-2-Element-Type
            (pair (Σ X (λ y → type-Decidable-Prop (pr1 t y))) (pr2 t))
            (pair (map-inv-equiv e x) p)
      cases-correct-transposition-conjugation-equiv (inr np) =
        ap (λ g → map-equiv g x) (inv (right-inverse-law-equiv e))

    correct-transposition-conjugation-equiv-list :
      (li : list
        ( Σ
          ( X → Decidable-Prop l3)
          ( λ P →
            has-cardinality-ℕ 2 (Σ X (type-Decidable-Prop ∘ P))))) →
      htpy-equiv
        ( permutation-list-transpositions
          ( map-list transposition-conjugation-equiv li))
        ( (e ∘e (permutation-list-transpositions li)) ∘e (inv-equiv e))
    correct-transposition-conjugation-equiv-list nil x =
      ap (λ g → map-equiv g x) (inv (right-inverse-law-equiv e))
    correct-transposition-conjugation-equiv-list (cons t li) x =
      ( correct-transposition-conjugation-equiv
        ( t)
        (map-equiv
          ( permutation-list-transpositions
            ( map-list transposition-conjugation-equiv li))
          ( x))) ∙
        ( ( ap
          ( map-equiv ((e ∘e transposition t) ∘e inv-equiv e))
          ( correct-transposition-conjugation-equiv-list li x)) ∙
          ( ap
            ( λ g →
              map-equiv
                ( ( ( (e ∘e transposition t) ∘e g) ∘e
                    ( permutation-list-transpositions li)) ∘e
                  ( inv-equiv e))
                ( x))
            ( left-inverse-law-equiv e)))
```

### For all `n : ℕ` and for each transposition of `Fin n`, there exists a matching transposition in `Fin (succ-ℕ n)`

```agda
Fin-succ-Fin-transposition :
  (n : ℕ) →
  ( Σ
    ( Fin n → Decidable-Prop lzero)
    ( λ P → has-cardinality-ℕ 2 (Σ (Fin n) (type-Decidable-Prop ∘ P)))) →
    ( Σ
      ( Fin (succ-ℕ n) → Decidable-Prop lzero)
      ( λ P →
        has-cardinality-ℕ 2
          ( Σ (Fin (succ-ℕ n)) (type-Decidable-Prop ∘ P))))
pr1 (Fin-succ-Fin-transposition n (pair P H)) (inl x) = P x
pr1 (Fin-succ-Fin-transposition n (pair P H)) (inr x) =
  pair empty (pair is-prop-empty is-decidable-empty)
pr2 (Fin-succ-Fin-transposition n (pair P H)) =
  apply-universal-property-trunc-Prop
    ( H)
    ( has-cardinality-ℕ-Prop 2
      ( Σ
        ( Fin (succ-ℕ n))
        ( type-Decidable-Prop ∘ pr1 (Fin-succ-Fin-transposition n (pair P H)))))
    ( λ h →
      unit-trunc-Prop
        ( ( pair f (is-equiv-is-invertible inv-f retraction-f section-f)) ∘e
          ( ( inv-right-unit-law-coproduct-is-empty
              ( Σ
                ( Fin n)
                ( type-Decidable-Prop ∘ P))
              ( Σ unit (λ _ → empty))
              ( map-right-absorption-product)) ∘e
            ( h))))
  where
  f :
    ( Σ (Fin n) (type-Decidable-Prop ∘ P)) + (Σ unit (λ _ → empty)) →
    Σ ( Fin (succ-ℕ n))
      ( λ x →
        type-Decidable-Prop
        (pr1 (Fin-succ-Fin-transposition n (pair P H)) x))
  f (inl (pair x p)) = pair (inl x) p
  inv-f :
    Σ ( Fin (succ-ℕ n))
      ( λ x →
        type-Decidable-Prop
        (pr1 (Fin-succ-Fin-transposition n (pair P H)) x)) →
    (Σ (Fin n) (type-Decidable-Prop ∘ P)) + (Σ unit (λ _ → empty))
  inv-f (pair (inl x) p) = inl (pair x p)
  retraction-f : (f ∘ inv-f) ~ id
  retraction-f (pair (inl x) p) = refl
  section-f : (inv-f ∘ f) ~ id
  section-f (inl (pair x p)) = refl

correct-Fin-succ-Fin-transposition :
  (n : ℕ) →
  (t : Σ
    ( Fin n → Decidable-Prop lzero)
    ( λ P → has-cardinality-ℕ 2 (Σ (Fin n) (type-Decidable-Prop ∘ P)))) →
  htpy-equiv
    ( transposition (Fin-succ-Fin-transposition n t))
    ( pr1
      ( map-equiv
        ( extend-equiv-Maybe (Fin-Set n))
        ( transposition t)))
correct-Fin-succ-Fin-transposition n t (inl x) with
  is-decidable-Decidable-Prop (pr1 t x)
correct-Fin-succ-Fin-transposition n t (inl x) | inl p =
    ap
      ( pr1)
      ( compute-swap-2-Element-Type
        ( pair
          ( Σ
            ( Fin (succ-ℕ n))
            ( type-Decidable-Prop ∘ pr1 (Fin-succ-Fin-transposition n t)))
          ( pr2 (Fin-succ-Fin-transposition n t)))
        ( pair (inl x) p)
        ( pair
          ( inl
            ( pr1
              ( map-swap-2-Element-Type
                ( pair
                  ( Σ (Fin n) (type-Decidable-Prop ∘ pr1 t))
                  ( pr2 t))
                ( pair x p))))
          ( pr2
            ( map-swap-2-Element-Type
              ( pair
                ( Σ (Fin n) (type-Decidable-Prop ∘ pr1 t))
                ( pr2 t))
              ( pair x p))))
        ( λ eq →
          has-no-fixed-points-swap-2-Element-Type
            ( pair (Σ (Fin n) (type-Decidable-Prop ∘ pr1 t)) (pr2 t))
            { pair x p}
            ( eq-pair-Σ
              ( is-injective-inl (inv (pr1 (pair-eq-Σ eq))))
              ( eq-is-prop (is-prop-type-Decidable-Prop (pr1 t x))))))
correct-Fin-succ-Fin-transposition n t (inl x) | inr np = refl
correct-Fin-succ-Fin-transposition n t (inr star) = refl

correct-Fin-succ-Fin-transposition-list :
  (n : ℕ)
  (l : list
    ( Σ
      ( Fin n → Decidable-Prop lzero)
      ( λ P →
        has-cardinality-ℕ 2 (Σ (Fin n) (type-Decidable-Prop ∘ P))))) →
  htpy-equiv
    ( permutation-list-transpositions
      ( map-list (Fin-succ-Fin-transposition n) l))
    ( pr1
      ( map-equiv
        ( extend-equiv-Maybe (Fin-Set n))
        ( permutation-list-transpositions l)))
correct-Fin-succ-Fin-transposition-list n nil =
  inv-htpy (id-map-coproduct (Fin n) unit)
correct-Fin-succ-Fin-transposition-list n (cons t l) x =
  correct-Fin-succ-Fin-transposition
    ( n)
    ( t)
    ( map-equiv
      ( permutation-list-transpositions
        ( map-list (Fin-succ-Fin-transposition n) l))
      ( x)) ∙
      ( (ap
        ( map-equiv
          ( pr1
            ( map-equiv (extend-equiv-Maybe (Fin-Set n)) (transposition t))))
        ( correct-Fin-succ-Fin-transposition-list n l x)) ∙
        ( inv
          ( comp-extend-equiv-Maybe
            ( Fin-Set n)
            ( transposition t)
            ( permutation-list-transpositions l)
            ( x))))
```

```agda
eq-transposition-precomp-standard-2-Element-Decidable-Subtype :
  {l : Level} {X : UU l} (H : has-decidable-equality X) →
  {x y : X} (np : x ≠ y) →
  Id
    ( precomp-equiv-2-Element-Decidable-Subtype
      ( standard-transposition H np)
      ( standard-2-Element-Decidable-Subtype H np))
    ( standard-2-Element-Decidable-Subtype H np)
eq-transposition-precomp-standard-2-Element-Decidable-Subtype
  {l} {X} H {x} {y} np =
  eq-pair-Σ
    ( eq-htpy
      ( λ z →
        eq-pair-Σ
          ( eq-equiv
            ( equiv-iff
              ( subtype-standard-2-Element-Decidable-Subtype H np
                ( map-inv-equiv (standard-transposition H np) z))
              ( subtype-standard-2-Element-Decidable-Subtype H np z)
              ( f z)
              ( g z)))
          ( eq-pair-Σ
            ( eq-is-prop
              ( is-prop-is-prop
                ( pr1 (pr1 (standard-2-Element-Decidable-Subtype H np) z))))
            ( eq-is-prop
              ( is-prop-is-decidable
                ( pr1
                  ( pr2
                    ( pr1
                      ( standard-2-Element-Decidable-Subtype H np)
                      ( z)))))))))
    ( eq-is-prop is-prop-type-trunc-Prop)
  where
  f :
    (z : X) →
    pr1
      ( pr1
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( standard-transposition H np)
          ( standard-2-Element-Decidable-Subtype H np)) z) →
    pr1 (pr1 (standard-2-Element-Decidable-Subtype H np) z)
  f z (inl p) =
    inr
      ( is-injective-equiv
        ( standard-transposition H np)
        ( ( right-computation-standard-transposition H np) ∙
          ( p)))
  f z (inr p) =
    inl
      ( is-injective-equiv
        ( standard-transposition H np)
        ( ( left-computation-standard-transposition H np) ∙
          ( p)))
  g :
    (z : X) →
    pr1 (pr1 (standard-2-Element-Decidable-Subtype H np) z) →
    pr1
      ( pr1
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( standard-transposition H np)
          ( standard-2-Element-Decidable-Subtype H np)) z)
  g z (inl p) =
    inr
      ( ( inv
        ( left-computation-standard-transposition H np)) ∙
        ( ap (map-standard-transposition H np) p))
  g z (inr p) =
    inl
      ( ( inv
        ( right-computation-standard-transposition H np)) ∙
        ( ap (map-standard-transposition H np) p))

eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtype :
  {l : Level} {X : UU l} (H : has-decidable-equality X) →
  {x y z w : X} (np : x ≠ y) (np' : z ≠ w) →
  x ≠ z → x ≠ w → y ≠ z → y ≠ w →
  precomp-equiv-2-Element-Decidable-Subtype
    ( standard-transposition H np)
    ( standard-2-Element-Decidable-Subtype H np') ＝
  standard-2-Element-Decidable-Subtype H np'
eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtype
  {l} {X} H {x} {y} {z} {w} np np' nq1 nq2 nq3 nq4 =
  eq-pair-Σ
    ( eq-htpy
      ( λ u →
        eq-pair-Σ
          ( eq-equiv
            ( equiv-iff
              ( subtype-standard-2-Element-Decidable-Subtype H np'
                ( map-inv-equiv (standard-transposition H np) u))
              ( subtype-standard-2-Element-Decidable-Subtype H np' u)
              ( f u)
              ( g u)))
          ( eq-pair-Σ
            ( eq-is-prop
              ( is-prop-is-prop
                ( pr1 (pr1 (standard-2-Element-Decidable-Subtype H np') u))))
            ( eq-is-prop
              ( is-prop-is-decidable
                ( pr1
                  ( pr2
                    ( pr1
                      ( standard-2-Element-Decidable-Subtype H np')
                      ( u)))))))))
    ( eq-is-prop is-prop-type-trunc-Prop)
  where
  f :
    (u : X) →
    pr1
      ( pr1
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( standard-transposition H np)
          ( standard-2-Element-Decidable-Subtype H np')) u) →
    pr1 (pr1 (standard-2-Element-Decidable-Subtype H np') u)
  f u (inl p) =
    inl
      ( is-injective-equiv
        ( standard-transposition H np)
        ( ( is-fixed-point-standard-transposition H np z nq1 nq3) ∙
          ( p)))
  f u (inr p) =
    inr
      ( is-injective-equiv
        ( standard-transposition H np)
        ( ( is-fixed-point-standard-transposition H np w nq2 nq4) ∙
          ( p)))
  g :
    (u : X) →
    pr1 (pr1 (standard-2-Element-Decidable-Subtype H np') u) →
    pr1
      ( pr1
        ( precomp-equiv-2-Element-Decidable-Subtype
          ( standard-transposition H np)
          ( standard-2-Element-Decidable-Subtype H np')) u)
  g u (inl p) =
    inl
      ( ( inv
        ( is-fixed-point-standard-transposition H np z nq1 nq3)) ∙
        ( ap (map-standard-transposition H np) p))
  g u (inr p) =
    inr
      ( ( inv
        ( is-fixed-point-standard-transposition H np w nq2 nq4)) ∙
        ( ap (map-standard-transposition H np) p))
```

```agda
module _
  {l1 : Level} (X : UU l1) (l l' : Level)
  where

  cases-eq-equiv-universes-transposition :
    ( P : 2-Element-Decidable-Subtype l X) (x : X) →
    ( d : is-decidable (is-in-2-Element-Decidable-Subtype P x)) →
    map-transposition' P x d ＝
    map-transposition
      ( map-equiv (equiv-universes-2-Element-Decidable-Subtype X l l') P)
      ( x)
  cases-eq-equiv-universes-transposition P x (inl p) =
    ( ap pr1
      ( inv
        ( compute-swap-2-Element-Decidable-Subtype
          ( map-equiv (equiv-universes-2-Element-Decidable-Subtype X l l') P)
          ( pair x (pr1 (iff-universes-decidable-subtype X l l' (pr1 P) x) p))
          ( pair
            ( pr1 (map-swap-2-Element-Decidable-Subtype P (pair x p)))
            ( pr1
              ( iff-universes-decidable-subtype X l l' (pr1 P)
                ( pr1 (map-swap-2-Element-Decidable-Subtype P (pair x p))))
              ( pr2 (map-swap-2-Element-Decidable-Subtype P (pair x p)))))
          ( λ q →
            has-no-fixed-points-swap-2-Element-Type
              ( 2-element-type-2-Element-Decidable-Subtype P)
              ( eq-pair-Σ
                ( pr1 (pair-eq-Σ (inv q)))
                ( eq-is-prop (is-prop-type-Decidable-Prop (pr1 P x)))))))) ∙
      ap
      ( λ d' →
        map-transposition'
          ( map-equiv
            ( equiv-universes-2-Element-Decidable-Subtype X l l')
            ( P))
          ( x)
          ( d'))
      { x = inl (pr1 (iff-universes-decidable-subtype X l l' (pr1 P) x) p)}
      { y =
        is-decidable-Decidable-Prop
          ( map-equiv (equiv-universes-decidable-subtype X l l') (pr1 P) x)}
      ( eq-is-prop
        ( is-prop-is-decidable
          ( is-prop-type-Decidable-Prop
            (map-equiv (equiv-universes-decidable-subtype X l l') (pr1 P) x))))
  cases-eq-equiv-universes-transposition P x (inr np) =
    ap
      ( λ d' →
        map-transposition'
          ( map-equiv
            ( equiv-universes-2-Element-Decidable-Subtype X l l')
            ( P))
          ( x)
          ( d'))
      { x = inr (np ∘ pr2 (iff-universes-decidable-subtype X l l' (pr1 P) x))}
      { y =
        is-decidable-Decidable-Prop
          ( map-equiv (equiv-universes-decidable-subtype X l l') (pr1 P) x)}
      ( eq-is-prop
        ( is-prop-is-decidable
          ( is-prop-type-Decidable-Prop
            (map-equiv (equiv-universes-decidable-subtype X l l') (pr1 P) x))))

  eq-equiv-universes-transposition :
    ( P : 2-Element-Decidable-Subtype l X) →
    transposition P ＝
    transposition
      ( map-equiv (equiv-universes-2-Element-Decidable-Subtype X l l') P)
  eq-equiv-universes-transposition P =
    eq-htpy-equiv
      ( λ x →
        cases-eq-equiv-universes-transposition P x
          ( is-decidable-Decidable-Prop (pr1 P x)))

  eq-equiv-universes-transposition-list :
    ( li : list (2-Element-Decidable-Subtype l X)) →
    permutation-list-transpositions li ＝
    permutation-list-transpositions
      ( map-list
        ( map-equiv (equiv-universes-2-Element-Decidable-Subtype X l l'))
        ( li))
  eq-equiv-universes-transposition-list nil = refl
  eq-equiv-universes-transposition-list (cons P li) =
    ap-binary
      ( _∘e_)
      ( eq-equiv-universes-transposition P)
      ( eq-equiv-universes-transposition-list li)
```

### Conjugate of a transposition is also a transposition

```agda
module _
  {l1 : Level}
  {X : UU l1}
  (H : has-decidable-equality X)
  {x y z : X}
  (npxy : x ≠ y)
  (npyz : y ≠ z)
  (npxz : x ≠ z)
  where

  cases-htpy-conjugate-transposition :
    (w : X) →
    ( is-decidable (w ＝ x)) →
    ( is-decidable (w ＝ y)) →
    ( is-decidable (w ＝ z)) →
    Id
      ( map-equiv
        ( standard-transposition H npyz ∘e
          ( standard-transposition H npxy ∘e standard-transposition H npyz))
        w)
      ( map-equiv ( standard-transposition H npxz) w)
  cases-htpy-conjugate-transposition x (inl refl) _ _ =
    ( ( ap
        ( λ w →
          map-equiv
            ( standard-transposition H npyz ∘e standard-transposition H npxy)
            ( w))
        ( is-fixed-point-standard-transposition
          ( H)
          ( npyz)
          ( x)
          ( npxy ∘ inv)
          ( npxz ∘ inv))) ∙
      ( ( ap
          ( λ w → map-equiv (standard-transposition H npyz) w)
          ( left-computation-standard-transposition H npxy)) ∙
        ( ( left-computation-standard-transposition H npyz) ∙
          ( ( inv (left-computation-standard-transposition H npxz))))))
  cases-htpy-conjugate-transposition y (inr neqx) (inl refl) _ =
    ( ( ap
        ( λ w →
          map-equiv
            ( standard-transposition H npyz ∘e standard-transposition H npxy)
            ( w))
        ( left-computation-standard-transposition H npyz)) ∙
      ( ( ap
          ( λ w → map-equiv (standard-transposition H npyz) w)
          ( is-fixed-point-standard-transposition H npxy z npxz npyz)) ∙
        ( ( right-computation-standard-transposition H npyz) ∙
          ( inv
            ( is-fixed-point-standard-transposition
              ( H)
              ( npxz)
              ( y)
              ( npxy)
              ( npyz ∘ inv))))))
  cases-htpy-conjugate-transposition z (inr neqx) (inr neqy) (inl refl) =
    ( ( ap
        ( λ w →
          map-equiv
            ( standard-transposition H npyz ∘e standard-transposition H npxy)
            ( w))
        ( right-computation-standard-transposition H npyz)) ∙
      ( ( ap
          ( λ w → map-equiv (standard-transposition H npyz) w)
          ( right-computation-standard-transposition H npxy)) ∙
        ( ( is-fixed-point-standard-transposition
            ( H)
            ( npyz)
            ( x)
            ( npxy ∘ inv)
            ( npxz ∘ inv)) ∙
          ( inv (right-computation-standard-transposition H npxz)))))
  cases-htpy-conjugate-transposition w (inr neqx) (inr neqy) (inr neqz) =
    ( ( ap
        ( λ w →
          map-equiv
            ( standard-transposition H npyz ∘e standard-transposition H npxy)
            ( w))
        ( is-fixed-point-standard-transposition
          ( H)
          ( npyz)
          ( w)
          ( neqy ∘ inv)
          ( neqz ∘ inv))) ∙
      ( ( ap
          ( λ w → map-equiv (standard-transposition H npyz) w)
          ( is-fixed-point-standard-transposition
            ( H)
            ( npxy)
            ( w)
            ( neqx ∘ inv)
            ( neqy ∘ inv))) ∙
        ( ( is-fixed-point-standard-transposition
            ( H)
            ( npyz)
            ( w)
            ( neqy ∘ inv)
            ( neqz ∘ inv)) ∙
          ( inv
            ( is-fixed-point-standard-transposition
              ( H)
              ( npxz)
              ( w)
              ( neqx ∘ inv)
              ( neqz ∘ inv))))))

  htpy-conjugate-transposition :
    htpy-equiv
      ( standard-transposition H npyz ∘e
        ( standard-transposition H npxy ∘e
          standard-transposition H npyz))
      ( standard-transposition H npxz)
  htpy-conjugate-transposition w =
    cases-htpy-conjugate-transposition w ( H w x) ( H w y) ( H w z)
```
