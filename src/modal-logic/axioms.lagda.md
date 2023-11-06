# Modal logic axioms

```agda
module modal-logic.axioms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.existential-quantification
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
  pr1 (ax-k f) = Σ (formula i) (λ a → Σ (formula i) (λ b → f ＝ a ⇒ b ⇒ a))
  pr2 (ax-k (a ⇒ b ⇒ a)) (_ , _ , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop
        ( a)
        ( b , refl)
        ( λ x y →
          ( is-prop-is-contr
            ( is-contr-Σ-is-prop
              ( b)
              ( ap _ ((eq-implication-left ∘ pr2) y))
              ( λ _ → is-set-formula i _ _)
              ( λ _ → eq-implication-left ∘ eq-implication-right))
            ( y)))
        ( λ _ → eq-implication-left ∘ pr2))
      ( a , b , refl)

  ax-s : formulas l i
  pr1 (ax-s f) =
    Σ
      ( formula i)
      ( λ a →
        ( Σ
          ( formula i)
          ( λ b → Σ (formula i) (λ c → f ＝ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c))))
  pr2 (ax-s ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)) (_ , _ , _ , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop
        ( a)
        ( b , c , refl)
        ( λ x y →
          ( is-prop-is-contr
            ( is-contr-Σ-is-prop
              ( pr1 y)
              ( pr2 y)
              ( λ z e →
                ( is-prop-is-contr
                  ( is-contr-Σ-is-prop
                    ( c)
                    ( ap-binary _
                      ( eq-implication-left (eq-implication-left (pr2 (pr2 y))))
                      ( eq-implication-left
                        ( eq-implication-right (eq-implication-left (pr2 e)))))
                    ( λ _ → is-set-formula i _ _)
                    ( λ _ →
                      ( eq-implication-right ∘
                        eq-implication-right ∘
                        eq-implication-right)))
                    ( e)))
              ( λ z e →
                _∙_
                ( inv
                  ( eq-implication-left
                    ( eq-implication-right
                      ( eq-implication-left (pr2 (pr2 y))))))
                ( eq-implication-left
                  ( eq-implication-right
                    ( eq-implication-left (pr2 e))))))
            ( y)))
        ( λ _ → eq-implication-left ∘ eq-implication-left ∘ pr2 ∘ pr2))
      ( a , b , c , refl)

  ax-n : formulas l i
  pr1 (ax-n f) =
    Σ (formula i) (λ a → Σ (formula i) (λ b → f ＝ □ (a ⇒ b) ⇒ □ a ⇒ □ b))
  pr2 (ax-n (□ (a ⇒ b) ⇒ □ a ⇒ □ b)) (_ , _ , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop
        ( a)
        ( b , refl)
        ( λ x y →
          ( is-prop-is-contr
            ( is-contr-Σ-is-prop
              ( b)
              ( ap _
                ( eq-box (eq-implication-left (eq-implication-right (pr2 y)))))
              ( λ _ → is-set-formula i _ _)
              ( λ _ → eq-box ∘ eq-implication-right ∘ eq-implication-right))
            ( y)))
        ( λ _ → eq-box ∘ eq-implication-left ∘ eq-implication-right ∘ pr2))
      ( a , b , refl)

  ax-dn : formulas l i
  pr1 (ax-dn f) = Σ (formula i) (λ a → f ＝ ~~ a ⇒ a)
  pr2 (ax-dn (((a ⇒ ⊥) ⇒ ⊥) ⇒ a)) (_ , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop
        ( a)
        ( refl)
        ( λ _ → is-set-formula i _ _)
        ( λ _ → eq-implication-right))
      ( a , refl)

module _
  {l1 l2 : Level}
  (i : Set l1)
  (w : UU l2)
  (l3 l4 : Level)
  where

  ax-k-soundness : soundness (ax-k i) (all-models w l3 i l4)
  ax-k-soundness (a ⇒ b ⇒ a) (_ , _ , refl) M _ x fa _ = fa

  ax-n-soundness : soundness (ax-n i) (all-models w l3 i l4)
  ax-n-soundness
    (□ (a ⇒ b) ⇒ □ a ⇒ □ b)
    (_ , _ , refl)
    M in-class x fab fa y r =
      fab y r (fa y r)

  ax-s-soundness : soundness (ax-s i) (all-models w l3 i l4)
  ax-s-soundness
    ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
    (_ , _ , _ , refl)
    M in-class x fabc fab fa =
      fabc fa (fab fa)

  ax-dn-soundness : soundness (ax-dn i) (decidable-models w l3 i l4)
  ax-dn-soundness (((a ⇒ ⊥) ⇒ ⊥) ⇒ a) (_ , refl) _ is-dec x f
    with (is-dec a x)
  ... | inl fa = fa
  ... | inr fna = raise-ex-falso _ (f (λ fa -> map-raise (fna fa)))
```
