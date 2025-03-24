# Symmetric difference of subtypes

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.symmetric-difference
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypes funext univalence truncations
open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.exclusive-sum funext univalence truncations
open import foundation.intersections-subtypes funext univalence truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions funext univalence truncations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes funext
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The **symmetric difference** of two [subtypes](foundation-core.subtypes.md) `A`
and `B` is the subtype that contains the elements that are either in `A` or in
`B` but not in both.

## Definition

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  symmetric-difference-subtype :
    subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  symmetric-difference-subtype P Q x =
    exclusive-sum-Prop (P x) (Q x)

  symmetric-difference-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  symmetric-difference-decidable-subtype P Q x =
    exclusive-sum-Decidable-Prop (P x) (Q x)
```

## Properties

### The coproduct of two decidable subtypes is equivalent to their symmetric difference plus two times their intersection

This is closely related to the _inclusion-exclusion principle_.

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  left-cases-equiv-symmetric-difference :
    (P : decidable-subtype l1 X) (Q : decidable-subtype l2 X) →
    (x : X) → type-Decidable-Prop (P x) →
    is-decidable (type-Decidable-Prop (Q x)) →
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
    (x : X) → type-Decidable-Prop (Q x) →
    is-decidable (type-Decidable-Prop (P x)) →
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
      ( is-decidable-Decidable-Prop (Q x))
  pr1 (equiv-symmetric-difference P Q) (inr (pair x q)) =
    right-cases-equiv-symmetric-difference P Q x q
      ( is-decidable-Decidable-Prop (P x))
  pr2 (equiv-symmetric-difference P Q) =
    is-equiv-is-invertible i r s
    where
    i :
      ( type-decidable-subtype (symmetric-difference-decidable-subtype P Q)) +
      ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
        ( type-decidable-subtype (intersection-decidable-subtype P Q))) →
      type-decidable-subtype P + type-decidable-subtype Q
    i (inl (pair x (inl (pair p nq)))) = inl (pair x p)
    i (inl (pair x (inr (pair q np)))) = inr (pair x q)
    i (inr (inl (pair x (pair p q)))) = inl (pair x p)
    i (inr (inr (pair x (pair p q)))) = inr (pair x q)
    r :
      (C :
        ( type-decidable-subtype (symmetric-difference-decidable-subtype P Q)) +
        ( ( type-decidable-subtype (intersection-decidable-subtype P Q)) +
          ( type-decidable-subtype (intersection-decidable-subtype P Q)))) →
      ((pr1 (equiv-symmetric-difference P Q)) ∘ i) C ＝ C
    r (inl (pair x (inl (pair p nq)))) =
      tr
        ( λ q' →
          ( left-cases-equiv-symmetric-difference P Q x p q') ＝
          ( inl (pair x (inl (pair p nq)))))
        ( eq-is-prop (is-prop-is-decidable (is-prop-type-Decidable-Prop (Q x))))
        ( refl)
    r (inl (pair x (inr (pair q np)))) =
      tr
        ( λ p' →
          ( right-cases-equiv-symmetric-difference P Q x q p') ＝
          ( inl (pair x (inr (pair q np)))))
        ( eq-is-prop (is-prop-is-decidable (is-prop-type-Decidable-Prop (P x))))
        ( refl)
    r (inr (inl (pair x (pair p q)))) =
      tr
        ( λ q' →
          (left-cases-equiv-symmetric-difference P Q x p q') ＝
          (inr (inl (pair x (pair p q)))))
        ( eq-is-prop (is-prop-is-decidable (is-prop-type-Decidable-Prop (Q x))))
        ( refl)
    r (inr (inr (pair x (pair p q)))) =
      tr
        ( λ p' →
          (right-cases-equiv-symmetric-difference P Q x q p') ＝
          (inr (inr (pair x (pair p q)))))
        ( eq-is-prop (is-prop-is-decidable (is-prop-type-Decidable-Prop (P x))))
        ( refl)
    left-cases-s :
      (x : X)
      (p : type-Decidable-Prop (P x))
      (q : is-decidable (type-Decidable-Prop (Q x))) →
      i (left-cases-equiv-symmetric-difference P Q x p q) ＝ inl (pair x p)
    left-cases-s x p (inl q) = refl
    left-cases-s x p (inr nq) = refl
    right-cases-s :
      (x : X)
      (q : type-Decidable-Prop (Q x))
      (p : is-decidable (type-Decidable-Prop (P x))) →
      i (right-cases-equiv-symmetric-difference P Q x q p) ＝ inr (pair x q)
    right-cases-s x q (inl p) = refl
    right-cases-s x q (inr np) = refl
    s :
      (C : type-decidable-subtype P + type-decidable-subtype Q) →
      (i ∘ pr1 (equiv-symmetric-difference P Q)) C ＝ C
    s (inl (pair x p)) =
      left-cases-s x p (is-decidable-Decidable-Prop (Q x))
    s (inr (pair x q)) =
      right-cases-s x q (is-decidable-Decidable-Prop (P x))
```

## See also

- [Complements of subtypes](foundation.complements-subtypes.md)
