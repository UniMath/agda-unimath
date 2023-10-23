# Modal logic K soundness

```agda
module modal-logic.K-soundness where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-function-types
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import modal-logic.K-syntax
open import modal-logic.formulas
open import modal-logic.kripke-semantics

open import univalent-combinatorics.decidable-dependent-function-types
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {w : Inhabited-Type l1} {i : Set l3}
  where

  private
    l = l1 ⊔ l2 ⊔ l3 ⊔ l4

  soundness :
    ((M , _) : decidable-model w l2 i l4)
    {a : formula i} →
    ⊢ a →
    type-Prop (M ⊨M a)
  soundness _ (ax-k _ _) x fa _ = fa
  soundness _ (ax-s _ _ _) x fabc fab fa = fabc fa (fab fa)
  soundness (_ , cl) (ax-dn a) x fdna with cl a x
  ... | inl fa = fa
  ... | inr nfa = raise-ex-falso _ (fdna (map-raise ∘ nfa))
  soundness _ (ax-n _ _) x fab fa y r = fab y r (fa y r)
  soundness CM (mp dab da) x = soundness CM dab x (soundness CM da x)
  soundness CM (nec d) x y _ = soundness CM d y

  module _
    ((M , w-is-finite) : finite-model w l2 i l4)
    (dec-val : ∀ n x → is-decidable (type-Prop (model-valuate M n x)))
    (dec-r : ∀ x y → is-decidable (model-relation M x y))
    where

    finite-model-is-decidable : is-decidable-model M
    finite-model-is-decidable (var n) x =
      is-decidable-raise _ _ (dec-val n x)
    finite-model-is-decidable ⊥ x =
      inr map-inv-raise
    finite-model-is-decidable (a ⇒ b) x =
      is-decidable-function-type
        ( finite-model-is-decidable a x)
        ( finite-model-is-decidable b x)
    finite-model-is-decidable (□ a) x =
      is-decidable-Π-is-finite w-is-finite
        ( λ y →
          is-decidable-function-type (dec-r x y)
          ( finite-model-is-decidable a y))

    finite-soundness : {a : formula i} → ⊢ a → type-Prop (M ⊨M a)
    finite-soundness = soundness (M , finite-model-is-decidable)

-- TODO: move to foundations
double-negation-LEM :
  {l : Level} →
  ((P : Prop l) → ¬¬ (type-Prop P) → (type-Prop P)) →
  LEM l
double-negation-LEM dnP P =
  dnP (is-decidable-Prop P) (λ ndec → ndec (inr (ndec ∘ inl)))

-- TODO: move to raising
compute-raise-function :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (A → B) ≃ (raise l A → raise l B)
compute-raise-function _ _ _ =
  equiv-function-type _ (compute-raise _ _) (compute-raise _ _)

raise-double-negation :
  (l : Level) {l1 : Level} {A : UU l1} →
  ¬¬ A →
  (raise l A → raise-empty l) → raise-empty l
raise-double-negation l =
  map-equiv-function-type _ (compute-raise-function _ _ _) (compute-raise _ _)
-- 2
-- map-equiv-function-type _
--   ( equiv-function-type _ (compute-raise _ _) (compute-raise _ _))
--   ( compute-raise _ _)
-- 3
-- raise-double-negation dnA rnA =
-- map-raise (dnA (map-inv-raise ∘ rnA ∘ map-raise))

full-soundness : UUω
full-soundness =
  {l1 l2 l3 l4 : Level}
  (W : Inhabited-Type l1)
  (i : Set l3)
  (M : kripke-model W l2 i l4)
  {a : formula i} →
  ⊢ a →
  type-Prop (M ⊨M a)

full-soundness-required-LEM : full-soundness → (l : Level) → LEM l
full-soundness-required-LEM sound l =
  double-negation-LEM required-double-negation
  where
  required-double-negation : (P : Prop l) → ¬¬ (type-Prop P) → type-Prop P
  required-double-negation P dnP =
    map-inv-raise
      ( sound
        ( unit , unit-trunc-Prop star)
        unit-Set
        ( model (frame (λ _ _ → empty-Prop)) (λ _ _ → P))
        ( ax-dn (var star))
        star
        ( raise-double-negation _ dnP))
```
