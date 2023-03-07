# Symmetric difference of subtypes

```agda
module foundation.symmetric-difference where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types hiding (inv)
open import foundation.intersections-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
open import foundation.xor
```

</details>

## Idea

The symmetric difference of two subtypes `A` and `B` is the subtypes that contains the elements that are either in `A` or in `B` but not in both.

## Definition

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  symmetric-difference-subtype :
    subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  symmetric-difference-subtype P Q x = xor-Prop (P x) (Q x)

  symmetric-difference-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  symmetric-difference-decidable-subtype P Q x = xor-decidable-Prop (P x) (Q x)
```

## Properties

### The coproduct of two decidable subtypes is equivalent to their symmetric difference plus two times their intersection

```
module _
  {l l1 l2 : Level} {X : UU l}
  where

  left-cases-equiv-symmetric-difference :
    (P : decidable-subtype l1 X) (Q : decidable-subtype l2 X) →
    (x : X) → type-decidable-Prop (P x) →
    is-decidable (type-decidable-Prop (Q x)) →
    ( type-decidable-subtype
      ( symmetric-difference-decidable-subtype P Q)) +
    ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
      ( type-decidable-subtype (intersection-decidable-subtype P Q)))
  left-cases-equiv-symmetric-difference P Q x p (inl q) =
    inr (inl (pair x (pair p q)))
  left-cases-equiv-symmetric-difference P Q x p (inr nq) =
    inl (pair x (inl (pair p nq)))

  right-cases-equiv-symmetric-difference :
    ( P : decidable-subtype l1 X) (Q : decidable-subtype l2 X) →
    (x : X) → type-decidable-Prop (Q x) →
    is-decidable (type-decidable-Prop (P x)) →
    ( type-decidable-subtype
      ( symmetric-difference-decidable-subtype P Q)) +
    ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
      ( type-decidable-subtype (intersection-decidable-subtype P Q)))
  right-cases-equiv-symmetric-difference P Q x q (inl p) =
    inr (inr (pair x (pair p q)))
  right-cases-equiv-symmetric-difference P Q x q (inr np) =
    inl (pair x (inr (pair q np)))

  equiv-symmetric-difference :
    (P : decidable-subtype l1 X) (Q : decidable-subtype l2 X) →
    ( (type-decidable-subtype P + type-decidable-subtype Q) ≃
      ( ( type-decidable-subtype (symmetric-difference-decidable-subtype P Q)) +
        ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
          ( type-decidable-subtype (intersection-decidable-subtype P Q)))))
  pr1 (equiv-symmetric-difference P Q) (inl (pair x p)) =
    left-cases-equiv-symmetric-difference P Q x p
      ( is-decidable-type-decidable-Prop (Q x))
  pr1 (equiv-symmetric-difference P Q) (inr (pair x q)) =
    right-cases-equiv-symmetric-difference P Q x q
      ( is-decidable-type-decidable-Prop (P x))
  pr2 (equiv-symmetric-difference P Q) =
    is-equiv-has-inverse inv retr sec
    where
    inv :
      ( type-decidable-subtype (symmetric-difference-decidable-subtype P Q)) +
      ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
        ( type-decidable-subtype (intersection-decidable-subtype P Q))) →
      type-decidable-subtype P + type-decidable-subtype Q
    inv (inl (pair x (inl (pair p nq)))) = inl (pair x p)
    inv (inl (pair x (inr (pair q np)))) = inr (pair x q)
    inv (inr (inl (pair x (pair p q)))) = inl (pair x p)
    inv (inr (inr (pair x (pair p q)))) = inr (pair x q)
    retr :
      (C :
        ( type-decidable-subtype (symmetric-difference-decidable-subtype P Q)) +
        ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
          ( type-decidable-subtype (intersection-decidable-subtype P Q)))) →
      ((pr1 (equiv-symmetric-difference P Q)) ∘ inv) C ＝ C
    retr (inl (pair x (inl (pair p nq)))) =
      tr
        ( λ q' →
          ( left-cases-equiv-symmetric-difference P Q x p q') ＝
          ( inl (pair x (inl (pair p nq)))))
        ( eq-is-prop (is-prop-is-decidable (is-prop-type-decidable-Prop (Q x))))
        ( refl)
    retr (inl (pair x (inr (pair q np)))) =
      tr
        ( λ p' →
          ( right-cases-equiv-symmetric-difference P Q x q p') ＝
          ( inl (pair x (inr (pair q np)))))
        ( eq-is-prop (is-prop-is-decidable (is-prop-type-decidable-Prop (P x))))
        ( refl)
    retr (inr (inl (pair x (pair p q)))) =
      tr
        ( λ q' →
          (left-cases-equiv-symmetric-difference P Q x p q') ＝
          (inr (inl (pair x (pair p q)))))
        ( eq-is-prop (is-prop-is-decidable (is-prop-type-decidable-Prop (Q x))))
        ( refl)
    retr (inr (inr (pair x (pair p q)))) =
      tr
        ( λ p' →
          (right-cases-equiv-symmetric-difference P Q x q p') ＝
          (inr (inr (pair x (pair p q)))))
        ( eq-is-prop (is-prop-is-decidable (is-prop-type-decidable-Prop (P x))))
        ( refl)
    left-cases-sec : (x : X) → (p : type-decidable-Prop (P x)) → (q : is-decidable (type-decidable-Prop (Q x))) →
      inv (left-cases-equiv-symmetric-difference P Q x p q) ＝ inl (pair x p)
    left-cases-sec x p (inl q) = refl
    left-cases-sec x p (inr nq) = refl
    right-cases-sec : (x : X) → (q : type-decidable-Prop (Q x)) → (p : is-decidable (type-decidable-Prop (P x))) →
      inv (right-cases-equiv-symmetric-difference P Q x q p) ＝ inr (pair x q)
    right-cases-sec x q (inl p) = refl
    right-cases-sec x q (inr np) = refl
    sec : (C : type-decidable-subtype P + type-decidable-subtype Q) →
      (inv ∘ pr1 (equiv-symmetric-difference P Q)) C ＝ C
    sec (inl (pair x p)) = left-cases-sec x p (is-decidable-type-decidable-Prop (Q x))
    sec (inr (pair x q)) = right-cases-sec x q (is-decidable-type-decidable-Prop (P x))
```
