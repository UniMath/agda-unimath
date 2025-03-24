# The symmetric identity types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.symmetric-identity-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction funext
open import foundation.identity-types funext
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.unordered-pairs funext univalence truncations

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.torsorial-type-families

open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

We construct a variant of the identity type equipped with a natural
`ℤ/2`-action.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  symmetric-Id :
    (a : unordered-pair A) → UU l
  symmetric-Id a =
    Σ A (λ x → (i : type-unordered-pair a) → x ＝ element-unordered-pair a i)

  module _
    (a : unordered-pair A)
    where

    Eq-symmetric-Id :
      (p q : symmetric-Id a) → UU l
    Eq-symmetric-Id (x , H) q =
      Σ (x ＝ pr1 q) (λ p → (i : type-unordered-pair a) → H i ＝ (p ∙ pr2 q i))

    refl-Eq-symmetric-Id :
      (p : symmetric-Id a) → Eq-symmetric-Id p p
    pr1 (refl-Eq-symmetric-Id (x , H)) = refl
    pr2 (refl-Eq-symmetric-Id (x , H)) i = refl

    is-torsorial-Eq-symmetric-Id :
      (p : symmetric-Id a) → is-torsorial (Eq-symmetric-Id p)
    is-torsorial-Eq-symmetric-Id (x , H) =
      is-torsorial-Eq-structure
        ( is-torsorial-Id x)
        ( x , refl)
        ( is-torsorial-htpy H)

    Eq-eq-symmetric-Id :
      (p q : symmetric-Id a) → p ＝ q → Eq-symmetric-Id p q
    Eq-eq-symmetric-Id p .p refl = refl-Eq-symmetric-Id p

    is-equiv-Eq-eq-symmetric-Id :
      (p q : symmetric-Id a) → is-equiv (Eq-eq-symmetric-Id p q)
    is-equiv-Eq-eq-symmetric-Id p =
      fundamental-theorem-id
        ( is-torsorial-Eq-symmetric-Id p)
        ( Eq-eq-symmetric-Id p)

    extensionality-symmetric-Id :
      (p q : symmetric-Id a) → (p ＝ q) ≃ Eq-symmetric-Id p q
    pr1 (extensionality-symmetric-Id p q) = Eq-eq-symmetric-Id p q
    pr2 (extensionality-symmetric-Id p q) = is-equiv-Eq-eq-symmetric-Id p q

    eq-Eq-symmetric-Id :
      (p q : symmetric-Id a) → Eq-symmetric-Id p q → p ＝ q
    eq-Eq-symmetric-Id p q = map-inv-equiv (extensionality-symmetric-Id p q)

  module _
    (a b : A)
    where

    map-compute-symmetric-Id :
      symmetric-Id (standard-unordered-pair a b) → a ＝ b
    map-compute-symmetric-Id (x , f) = inv (f (zero-Fin 1)) ∙ f (one-Fin 1)

    map-inv-compute-symmetric-Id :
      a ＝ b → symmetric-Id (standard-unordered-pair a b)
    pr1 (map-inv-compute-symmetric-Id p) = a
    pr2 (map-inv-compute-symmetric-Id p) (inl (inr _)) = refl
    pr2 (map-inv-compute-symmetric-Id p) (inr _) = p

    is-section-map-inv-compute-symmetric-Id :
      ( map-compute-symmetric-Id ∘ map-inv-compute-symmetric-Id) ~ id
    is-section-map-inv-compute-symmetric-Id refl = refl

    abstract
      is-retraction-map-inv-compute-symmetric-Id :
        ( map-inv-compute-symmetric-Id ∘ map-compute-symmetric-Id) ~ id
      is-retraction-map-inv-compute-symmetric-Id (x , f) =
        eq-Eq-symmetric-Id
          ( standard-unordered-pair a b)
          ( map-inv-compute-symmetric-Id (map-compute-symmetric-Id (x , f)))
          ( x , f)
          ( ( inv (f (zero-Fin 1))) ,
            ( λ where
              ( inl (inr _)) → inv (left-inv (f (zero-Fin 1)))
              ( inr _) → refl))

    is-equiv-map-compute-symmetric-Id :
      is-equiv (map-compute-symmetric-Id)
    is-equiv-map-compute-symmetric-Id =
      is-equiv-is-invertible
        ( map-inv-compute-symmetric-Id)
        ( is-section-map-inv-compute-symmetric-Id)
        ( is-retraction-map-inv-compute-symmetric-Id)

    compute-symmetric-Id :
      symmetric-Id (standard-unordered-pair a b) ≃ (a ＝ b)
    pr1 (compute-symmetric-Id) = map-compute-symmetric-Id
    pr2 (compute-symmetric-Id) = is-equiv-map-compute-symmetric-Id
```

## Properties

### The action of functions on symmetric identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-symmetric-Id :
    (f : A → B) (a : unordered-pair A) →
    symmetric-Id a → symmetric-Id (map-unordered-pair f a)
  map-symmetric-Id f a =
    map-Σ
      ( λ b → (x : type-unordered-pair a) → b ＝ f (element-unordered-pair a x))
      ( f)
      ( λ x → map-Π (λ i → ap f))
```

### The action of equivalences on symmetric identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-symmetric-Id :
    (e : A ≃ B) (a : unordered-pair A) →
    symmetric-Id a ≃ symmetric-Id (map-equiv-unordered-pair e a)
  equiv-symmetric-Id e a =
    equiv-Σ
      ( λ b →
        (x : type-unordered-pair a) →
        b ＝ map-equiv e (element-unordered-pair a x))
      ( e)
      ( λ x →
        equiv-Π-equiv-family (λ i → equiv-ap e x (element-unordered-pair a i)))

  map-equiv-symmetric-Id :
    (e : A ≃ B) (a : unordered-pair A) →
    symmetric-Id a → symmetric-Id (map-equiv-unordered-pair e a)
  map-equiv-symmetric-Id e a = map-equiv (equiv-symmetric-Id e a)

id-equiv-symmetric-Id :
  {l : Level} {A : UU l} (a : unordered-pair A) →
  map-equiv-symmetric-Id id-equiv a ~ id
id-equiv-symmetric-Id a (x , H) =
  eq-pair-eq-fiber (eq-htpy (λ u → ap-id (H u)))
```

### Transport in the symmetric identity type along observational equality of unordered pairs

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-tr-symmetric-Id :
    (p q : unordered-pair A) → Eq-unordered-pair p q →
    symmetric-Id p ≃ symmetric-Id q
  equiv-tr-symmetric-Id (X , f) (Y , g) (e , H) =
    equiv-tot (λ a → equiv-Π (λ x → a ＝ g x) e (λ x → equiv-concat' a (H x)))

  tr-symmetric-Id :
    (p q : unordered-pair A)
    (e : type-unordered-pair p ≃ type-unordered-pair q) →
    (element-unordered-pair p ~ (element-unordered-pair q ∘ map-equiv e)) →
    symmetric-Id p → symmetric-Id q
  tr-symmetric-Id p q e H = map-equiv (equiv-tr-symmetric-Id p q (pair e H))

  compute-pr2-tr-symmetric-Id :
    (p q : unordered-pair A)
    (e : type-unordered-pair p ≃ type-unordered-pair q) →
    (H : element-unordered-pair p ~ (element-unordered-pair q ∘ map-equiv e)) →
    {a : A}
    (K : (x : type-unordered-pair p) → a ＝ element-unordered-pair p x) →
    (x : type-unordered-pair p) →
    pr2 (tr-symmetric-Id p q e H (a , K)) (map-equiv e x) ＝ (K x ∙ H x)
  compute-pr2-tr-symmetric-Id (X , f) (Y , g) e H {a} =
    compute-map-equiv-Π (λ x → a ＝ g x) e (λ x → equiv-concat' a (H x))

  refl-Eq-unordered-pair-tr-symmetric-Id :
    (p : unordered-pair A) →
    tr-symmetric-Id p p id-equiv refl-htpy ~ id
  refl-Eq-unordered-pair-tr-symmetric-Id p (a , K) =
    eq-pair-eq-fiber
      ( eq-htpy
        ( ( compute-pr2-tr-symmetric-Id p p id-equiv refl-htpy K) ∙h
          ( right-unit-htpy)))
```
