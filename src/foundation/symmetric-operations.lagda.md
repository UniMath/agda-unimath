# Symmetric operations

```agda
module foundation.symmetric-operations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.propositional-truncations
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels
open import foundation.unordered-pairs

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Recall that there is a standard unordered pairing operation
`{-,-} : A → (A → unordered-pair A)`. This induces for any type `B` a map

```text
  λ f x y → f {x,y} : (unordered-pair A → B) → (A → A → B)
```

A binary operation `μ : A → A → B` is symmetric if it extends to an operation
`μ̃ : unordered-pair A → B` along `{-,-}`. That is, a binary operation `μ` is
symmetric if there is an operation `μ̃` on the unordered pairs in `A`, such that
`μ̃({x,y}) = μ(x,y)` for all `x, y : A`. Symmetric operations can be understood
to be fully coherent commutative operations. One can check that if `B` is a set,
then `μ` has such an extension if and only if it is commutative in the usual
algebraic sense.

## Definition

### The (incoherent) algebraic condition of commutativity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-commutative : (A → A → B) → UU (l1 ⊔ l2)
  is-commutative f = (x y : A) → f x y ＝ f y x

is-commutative-Prop :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) →
  (A → A → type-Set B) → Prop (l1 ⊔ l2)
is-commutative-Prop B f =
  Π-Prop _ (λ x → Π-Prop _ (λ y → Id-Prop B (f x y) (f y x)))
```

### Commutative operations

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  symmetric-operation : UU (lsuc lzero ⊔ l1 ⊔ l2)
  symmetric-operation = unordered-pair A → B

  map-symmetric-operation : symmetric-operation → A → A → B
  map-symmetric-operation f x y =
    f (standard-unordered-pair x y)
```

## Properties

### The restriction of a commutative operation to the standard unordered pairs is commutative

```agda
is-commutative-symmetric-operation :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : symmetric-operation A B) →
  is-commutative (λ x y → f (standard-unordered-pair x y))
is-commutative-symmetric-operation f x y =
  ap f (is-commutative-standard-unordered-pair x y)
```

### A binary operation from `A` to `B` is commutative if and only if it extends to the unordered pairs in `A`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2)
  where

  is-weakly-constant-on-equivalences-is-commutative :
    (f : A → A → type-Set B) (H : is-commutative f) →
    (X : UU lzero) (p : X → A) (e e' : Fin 2 ≃ X) →
    (htpy-equiv e e') + (htpy-equiv e (e' ∘e equiv-succ-Fin 2)) →
    ( f (p (map-equiv e (zero-Fin 1))) (p (map-equiv e (one-Fin 1)))) ＝
    ( f (p (map-equiv e' (zero-Fin 1))) (p (map-equiv e' (one-Fin 1))))
  is-weakly-constant-on-equivalences-is-commutative f H X p e e' (inl K) =
    ap-binary f (ap p (K (zero-Fin 1))) (ap p (K (one-Fin 1)))
  is-weakly-constant-on-equivalences-is-commutative f H X p e e' (inr K) =
    ( ap-binary f (ap p (K (zero-Fin 1))) (ap p (K (one-Fin 1)))) ∙
    ( H (p (map-equiv e' (one-Fin 1))) (p (map-equiv e' (zero-Fin 1))))

  symmetric-operation-is-commutative :
    (f : A → A → type-Set B) → is-commutative f →
    symmetric-operation A (type-Set B)
  symmetric-operation-is-commutative f H (pair (pair X K) p) =
    map-universal-property-set-quotient-trunc-Prop B
      ( λ e → f (p (map-equiv e (zero-Fin 1))) (p (map-equiv e (one-Fin 1))))
      ( λ e e' →
        is-weakly-constant-on-equivalences-is-commutative f H X p e e'
          ( map-equiv-coproduct
            ( inv-equiv (equiv-ev-zero-htpy-equiv-Fin-2 (pair X K) e e'))
            ( inv-equiv (equiv-ev-zero-htpy-equiv-Fin-2
              ( pair X K)
              ( e)
              ( e' ∘e equiv-succ-Fin 2)))
            ( decide-value-equiv-Fin-2
              ( pair X K)
              ( e')
              ( map-equiv e (zero-Fin 1)))))
      ( K)

  compute-symmetric-operation-is-commutative :
    (f : A → A → type-Set B) (H : is-commutative f) (x y : A) →
    symmetric-operation-is-commutative f H (standard-unordered-pair x y) ＝
    f x y
  compute-symmetric-operation-is-commutative f H x y =
    htpy-universal-property-set-quotient-trunc-Prop B
      ( λ e → f (p (map-equiv e (zero-Fin 1))) (p (map-equiv e (one-Fin 1))))
      ( λ e e' →
        is-weakly-constant-on-equivalences-is-commutative f H (Fin 2) p e e'
          ( map-equiv-coproduct
            ( inv-equiv
              ( equiv-ev-zero-htpy-equiv-Fin-2
                ( Fin-Type-With-Cardinality-ℕ 2)
                ( e)
                ( e')))
            ( inv-equiv (equiv-ev-zero-htpy-equiv-Fin-2
              ( Fin-Type-With-Cardinality-ℕ 2)
              ( e)
              ( e' ∘e equiv-succ-Fin 2)))
            ( decide-value-equiv-Fin-2
              ( Fin-Type-With-Cardinality-ℕ 2)
              ( e')
              ( map-equiv e (zero-Fin 1)))))
      ( id-equiv)
    where
    p : Fin 2 → A
    p = pr2 (standard-unordered-pair x y)
```

### Characterization of equality of symmetric operations into sets

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : Set l2)
  (f : symmetric-operation A (type-Set B))
  where

  htpy-symmetric-operation-Set-Prop :
    (g : symmetric-operation A (type-Set B)) → Prop (l1 ⊔ l2)
  htpy-symmetric-operation-Set-Prop g =
    Π-Prop A
      ( λ x →
        Π-Prop A
          ( λ y →
            Id-Prop B
              ( map-symmetric-operation A (type-Set B) f x y)
              ( map-symmetric-operation A (type-Set B) g x y)))

  htpy-symmetric-operation-Set :
    (g : symmetric-operation A (type-Set B)) → UU (l1 ⊔ l2)
  htpy-symmetric-operation-Set g =
    type-Prop (htpy-symmetric-operation-Set-Prop g)

  center-total-htpy-symmetric-operation-Set :
    Σ ( symmetric-operation A (type-Set B))
      ( htpy-symmetric-operation-Set)
  pr1 center-total-htpy-symmetric-operation-Set = f
  pr2 center-total-htpy-symmetric-operation-Set x y = refl

  abstract
    contraction-total-htpy-symmetric-operation-Set :
      ( t :
        Σ ( symmetric-operation A (type-Set B))
          ( htpy-symmetric-operation-Set)) →
      center-total-htpy-symmetric-operation-Set ＝ t
    contraction-total-htpy-symmetric-operation-Set (g , H) =
      eq-type-subtype
        htpy-symmetric-operation-Set-Prop
        ( eq-htpy
          ( λ p →
            apply-universal-property-trunc-Prop
              ( is-surjective-standard-unordered-pair p)
              ( Id-Prop B (f p) (g p))
              ( λ where (x , y , refl) → H x y)))

  is-torsorial-htpy-symmetric-operation-Set :
    is-torsorial (htpy-symmetric-operation-Set)
  pr1 is-torsorial-htpy-symmetric-operation-Set =
    center-total-htpy-symmetric-operation-Set
  pr2 is-torsorial-htpy-symmetric-operation-Set =
    contraction-total-htpy-symmetric-operation-Set

  htpy-eq-symmetric-operation-Set :
    (g : symmetric-operation A (type-Set B)) →
    (f ＝ g) → htpy-symmetric-operation-Set g
  htpy-eq-symmetric-operation-Set g refl x y = refl

  is-equiv-htpy-eq-symmetric-operation-Set :
    (g : symmetric-operation A (type-Set B)) →
    is-equiv (htpy-eq-symmetric-operation-Set g)
  is-equiv-htpy-eq-symmetric-operation-Set =
    fundamental-theorem-id
      is-torsorial-htpy-symmetric-operation-Set
      htpy-eq-symmetric-operation-Set

  extensionality-symmetric-operation-Set :
    (g : symmetric-operation A (type-Set B)) →
    (f ＝ g) ≃ htpy-symmetric-operation-Set g
  pr1 (extensionality-symmetric-operation-Set g) =
    htpy-eq-symmetric-operation-Set g
  pr2 (extensionality-symmetric-operation-Set g) =
    is-equiv-htpy-eq-symmetric-operation-Set g

  eq-htpy-symmetric-operation-Set :
    (g : symmetric-operation A (type-Set B)) →
    htpy-symmetric-operation-Set g → (f ＝ g)
  eq-htpy-symmetric-operation-Set g =
    map-inv-equiv (extensionality-symmetric-operation-Set g)
```

### The type of commutative operations into a set is equivalent to the type of symmetric operations

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : Set l2)
  where

  map-compute-symmetric-operation-Set :
    symmetric-operation A (type-Set B) → Σ (A → A → type-Set B) is-commutative
  pr1 (map-compute-symmetric-operation-Set f) =
    map-symmetric-operation A (type-Set B) f
  pr2 (map-compute-symmetric-operation-Set f) =
    is-commutative-symmetric-operation f

  map-inv-compute-symmetric-operation-Set :
    Σ (A → A → type-Set B) is-commutative → symmetric-operation A (type-Set B)
  map-inv-compute-symmetric-operation-Set (f , H) =
    symmetric-operation-is-commutative B f H

  is-section-map-inv-compute-symmetric-operation-Set :
    ( map-compute-symmetric-operation-Set ∘
      map-inv-compute-symmetric-operation-Set) ~ id
  is-section-map-inv-compute-symmetric-operation-Set (f , H) =
    eq-type-subtype
      ( is-commutative-Prop B)
      ( eq-htpy
        ( λ x →
          eq-htpy
            ( λ y →
              compute-symmetric-operation-is-commutative B f H x y)))

  is-retraction-map-inv-compute-symmetric-operation-Set :
    ( map-inv-compute-symmetric-operation-Set ∘
      map-compute-symmetric-operation-Set) ~ id
  is-retraction-map-inv-compute-symmetric-operation-Set g =
    eq-htpy-symmetric-operation-Set A B
      ( map-inv-compute-symmetric-operation-Set
        ( map-compute-symmetric-operation-Set g))
      ( g)
      ( compute-symmetric-operation-is-commutative B
        ( map-symmetric-operation A (type-Set B) g)
        ( is-commutative-symmetric-operation g))

  is-equiv-map-compute-symmetric-operation-Set :
    is-equiv map-compute-symmetric-operation-Set
  is-equiv-map-compute-symmetric-operation-Set =
    is-equiv-is-invertible
      map-inv-compute-symmetric-operation-Set
      is-section-map-inv-compute-symmetric-operation-Set
      is-retraction-map-inv-compute-symmetric-operation-Set

  compute-symmetric-operation-Set :
    symmetric-operation A (type-Set B) ≃ Σ (A → A → type-Set B) is-commutative
  pr1 compute-symmetric-operation-Set =
    map-compute-symmetric-operation-Set
  pr2 compute-symmetric-operation-Set =
    is-equiv-map-compute-symmetric-operation-Set
```
