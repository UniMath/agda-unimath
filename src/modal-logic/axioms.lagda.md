# Modal logic axioms

```agda
module modal-logic.axioms where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.soundness
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l : Level} (i : Set l)
  where

  ax-k : formulas l i
  ax-k (a₁ ⇒ b ⇒ a₂) = Id-formula-Prop a₁ a₂
  {-# CATCHALL #-}
  ax-k _ = raise-empty-Prop l

  ax-s : formulas l i
  ax-s ((a₁ ⇒ b₁ ⇒ c₁) ⇒ (a₂ ⇒ b₂) ⇒ a₃ ⇒ c₂) =
    Id-formula-Prop a₁ a₂ ∧
    Id-formula-Prop a₂ a₃ ∧
    Id-formula-Prop b₁ b₂ ∧
    Id-formula-Prop c₁ c₂
  {-# CATCHALL #-}
  ax-s _ = raise-empty-Prop l

  ax-n : formulas l i
  ax-n (□ (a₁ ⇒ b₁) ⇒ □ a₂ ⇒ □ b₂) =
    Id-formula-Prop a₁ a₂ ∧
    Id-formula-Prop b₁ b₂
  {-# CATCHALL #-}
  ax-n _ = raise-empty-Prop l

  ax-dn : formulas l i
  ax-dn (((a₁ ⇒ ⊥) ⇒ ⊥) ⇒ a₂) = Id-formula-Prop a₁ a₂
  {-# CATCHALL #-}
  ax-dn _ = raise-empty-Prop l

module _
  {l1 l2 : Level}
  (i : Set l1)
  (w : Inhabited-Type l2)
  (l3 l4 : Level)
  where

  ax-k-soundness : soundness (ax-k i) (all-models w l3 i l4)
  ax-k-soundness (a₁ ⇒ b ⇒ a₁) refl M in-class x fa _ = fa
  ax-k-soundness (var _) (map-raise ())
  ax-k-soundness ⊥ (map-raise ())
  ax-k-soundness (□ _) (map-raise ())
  ax-k-soundness (_ ⇒ var _) (map-raise ())
  ax-k-soundness (_ ⇒ ⊥) (map-raise ())
  ax-k-soundness (_ ⇒ □ _) (map-raise ())

  ax-n-soundness : soundness (ax-n i) (all-models w l3 i l4)
  ax-n-soundness
    (□ (a₁ ⇒ b₁) ⇒ □ a₁ ⇒ □ b₁)
    (refl , refl)
    M in-class x fab fa y r =
      fab y r (fa y r)
  ax-n-soundness (var _) (map-raise ())
  ax-n-soundness ⊥ (map-raise ())
  ax-n-soundness (□ _) (map-raise ())
  ax-n-soundness (var _ ⇒ _) (map-raise ())
  ax-n-soundness (⊥ ⇒ _) (map-raise ())
  ax-n-soundness ((_ ⇒ _) ⇒ _) (map-raise ())
  ax-n-soundness (□ var _ ⇒ _) (map-raise ())
  ax-n-soundness (□ ⊥ ⇒ _) (map-raise ())
  ax-n-soundness (□ □ _ ⇒ _) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ var _) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ ⊥) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ □ _) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ var _ ⇒ _) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ ⊥ ⇒ _) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ (_ ⇒ _) ⇒ _) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ □ _ ⇒ var _) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ □ _ ⇒ ⊥) (map-raise ())
  ax-n-soundness (□ (_ ⇒ _) ⇒ □ _ ⇒ _ ⇒ _) (map-raise ())

  ax-s-soundness : soundness (ax-s i) (all-models w l3 i l4)
  ax-s-soundness
    ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
    (refl , refl , refl , refl)
    M in-class x fabc fab fa =
      fabc fa (fab fa)
  ax-s-soundness (var _) (map-raise ())
  ax-s-soundness ⊥ (map-raise ())
  ax-s-soundness (□ _) (map-raise ())
  ax-s-soundness (var _ ⇒ _) (map-raise ())
  ax-s-soundness (⊥ ⇒ _) (map-raise ())
  ax-s-soundness (□ _ ⇒ _) (map-raise ())
  ax-s-soundness ((_ ⇒ var _) ⇒ _) (map-raise ())
  ax-s-soundness ((_ ⇒ ⊥) ⇒ _) (map-raise ())
  ax-s-soundness ((_ ⇒ □ _) ⇒ _) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ var _) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ ⊥) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ □ _) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ var _ ⇒ _) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ ⊥ ⇒ _) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ □ _ ⇒ _) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ (_ ⇒ _) ⇒ var _) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ (_ ⇒ _) ⇒ ⊥) (map-raise ())
  ax-s-soundness ((_ ⇒ _ ⇒ _) ⇒ (_ ⇒ _) ⇒ □ _) (map-raise ())

  ax-dn-soundness : soundness (ax-dn i) (decidable-models w l3 i l4)
  ax-dn-soundness (((a ⇒ ⊥) ⇒ ⊥) ⇒ a) refl M is-dec x f with is-dec a x
  ... | inl fa = fa
  ... | inr fna = raise-ex-falso _ (f (λ fa → map-raise (fna fa)))
  ax-dn-soundness (var _) (map-raise ())
  ax-dn-soundness ⊥ (map-raise ())
  ax-dn-soundness (□ _) (map-raise ())
  ax-dn-soundness (var _ ⇒ _) (map-raise ())
  ax-dn-soundness (⊥ ⇒ _) (map-raise ())
  ax-dn-soundness (□ _ ⇒ _) (map-raise ())
  ax-dn-soundness ((var _ ⇒ _) ⇒ _) (map-raise ())
  ax-dn-soundness ((⊥ ⇒ _) ⇒ _) (map-raise ())
  ax-dn-soundness ((□ _ ⇒ _) ⇒ _) (map-raise ())
  ax-dn-soundness (((_ ⇒ var _) ⇒ _) ⇒ _) (map-raise ())
  ax-dn-soundness (((_ ⇒ _ ⇒ _) ⇒ _) ⇒ _) (map-raise ())
  ax-dn-soundness (((_ ⇒ □ _) ⇒ _) ⇒ _) (map-raise ())
  ax-dn-soundness (((_ ⇒ ⊥) ⇒ var _) ⇒ _) (map-raise ())
  ax-dn-soundness (((_ ⇒ ⊥) ⇒ _ ⇒ _) ⇒ _) (map-raise ())
  ax-dn-soundness (((_ ⇒ ⊥) ⇒ □ _) ⇒ _) (map-raise ())
```
