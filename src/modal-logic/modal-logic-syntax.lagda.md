# Modal logic syntax

```agda
module modal-logic.modal-logic-syntax where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.binary-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.inhabited-types
open import foundation.coproduct-types
open import foundation.function-types
open import foundation.empty-types
open import foundation.unit-type
open import foundation.negation
open import foundation.double-negation
open import foundation.propositional-truncations

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.decidable-dependent-function-types
-- open import univalent-combinatorics.dependent-function-types
```

</details>

## Idea

TODO

## Definition

```agda
-- I'am not found in lib
module _
  {a : Level} (l : Level)
  where

  record Lift (A : UU a) : UU (a ⊔ l) where
    constructor lift
    field lower : A
  open Lift public

  Lift-Prop : Prop a → Prop (a ⊔ l)
  pr1 (Lift-Prop A) = Lift (type-Prop A)
  pr2 (Lift-Prop A) =
    is-prop-equiv'
      (lift , is-equiv-is-invertible lower (λ _ → refl) (λ _ → refl))
      (is-prop-type-Prop A)

  is-decidable-Lift : {A : UU a} → is-decidable A → is-decidable (Lift A)
  is-decidable-Lift (inl a) = inl (lift a)
  is-decidable-Lift (inr na) = inr (na ∘ lower)

LEM : (l : Level) → UU (lsuc l)
LEM l = (T : UU l) → is-decidable T
```

**Syntax**

```agda
module _
  {l : Level}
  (i : UU l)
  where

  data formula : UU l where
    var : i → formula
    ⊥ : formula
    _⇒_ : formula → formula → formula
    □ : formula → formula

module _
  {l : Level}
  {i : UU l}
  where

  ~ : formula i → formula i
  ~ a = a ⇒ ⊥

  _∨_ : formula i → formula i → formula i
  a ∨ b = (~ a) ⇒ b

  _∧_ : formula i → formula i → formula i
  a ∧ b = ~ (a ⇒ (~ b))

  ⊤ : formula i
  ⊤ = ~ ⊥

  ◇ : formula i → formula i
  ◇ a = ~ (□ (~ a))

  data ⊢ : formula i → UU l where
    ax-k : {a b : formula i} → ⊢ (a ⇒ (b ⇒ a))
    ax-s : {a b c : formula i} → ⊢ ((a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c)))
    ax-dn : {a : formula i} → ⊢ ((~ (~ a)) ⇒ a)
    ax-n : {a b : formula i} → ⊢ ((□ (a ⇒ b)) ⇒ ((□ a) ⇒ (□ b)))
    mp : {a b : formula i} → ⊢ (a ⇒ b) → ⊢ a → ⊢ b
    nec : {a : formula i} → ⊢ a → ⊢ (□ a)
```

**Semantics**

```agda
module _
  {l1 : Level}
  (w : UU l1)
  where

  record kripke-frame : UU (lsuc l1) where
    constructor frame
    field
      R : Relation l1 w
      frame-inhabited : is-inhabited w
  open kripke-frame public

module _
  {l1 l2 : Level}
  (w : UU l1) (i : UU l2)
  (l3 : Level)
  where

  record kripke-model : UU (lsuc l1 ⊔ l2 ⊔ lsuc l3) where
    constructor model
    field
      F : kripke-frame w
      V : i → w → UU l3
  open kripke-model public

  finite-model : UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
  finite-model = kripke-model × is-finite w


module _
  {l1 l2 l3 : Level}
  {w : UU l1} {i : UU l2}
  where

  private
    l = l1 ⊔ l2 ⊔ l3

  _,_⊨_ : kripke-model w i l3 → w → formula i → UU l
  M , x ⊨ var n = Lift l (V M n x)
  M , x ⊨ ⊥ = Lift l empty
  M , x ⊨ (a ⇒ b) = M , x ⊨ a → M , x ⊨ b
  M , x ⊨ (□ a) = ∀ y → R (F M) x y → M , y ⊨ a

  _,_⊭_ : kripke-model w i l3 → w → formula i → UU l
  M , x ⊭ a = ¬ (M , x ⊨ a)

  _⊨M_ : kripke-model w i l3 → formula i → UU l
  M ⊨M a = ∀ x → M , x ⊨ a

  _⊭M_ : kripke-model w i l3 → formula i → UU l
  M ⊭M a = ¬ (M ⊨M a)
```

**Soundness**

```agda
  is-classical : kripke-model w i l3 → UU l
  is-classical M = ∀ a x → is-decidable (M , x ⊨ a)

  soundness : {a : formula i}
            → ⊢ a
            → (M : kripke-model w i l3)
            → is-classical M
            → M ⊨M a
  soundness ax-k M dec x = λ fa _ → fa
  soundness ax-s M dec x = λ fabc fab fa → fabc fa (fab fa)
  soundness {_ ⇒ a} ax-dn M dec x with dec a x
  ... | inl fa = λ _ → fa
  ... | inr nfa = λ fnna → ex-falso (lower (fnna (λ fa → lift (nfa fa))))
  soundness ax-n M dec x = λ fab fa y r → fab y r (fa y r)
  soundness (mp dab db) M dec x = soundness dab M dec x (soundness db M dec x)
  soundness (nec d) M dec x y _ = soundness d M dec y

  finite-is-classical : ((M , _) : finite-model w i l3)
                      → (∀ n x → is-decidable (V M n x))
                      → (∀ x y → is-decidable (R (F M) x y))
                      → is-classical M
  finite-is-classical (M , is-fin) dec-val dec-r (var n) x =
    is-decidable-Lift _ (dec-val n x)
  finite-is-classical (M , is-fin) dec-val dec-r ⊥ x =
    inr (λ ())
  finite-is-classical (M , is-fin) dec-val dec-r (a ⇒ b) x =
    is-decidable-function-type
      (finite-is-classical (M , is-fin) dec-val dec-r a x)
      (finite-is-classical (M , is-fin) dec-val dec-r b x)
  finite-is-classical (M , is-fin) dec-val dec-r (□ a) x =
    is-decidable-Π-is-finite is-fin
      (λ y →
        is-decidable-function-type (dec-r x y)
        ((finite-is-classical (M , is-fin) dec-val dec-r a y)))

  finite-soundness : ((M , _) : finite-model w i l3)
                   → (∀ n x → is-decidable (V M n x))
                   → (∀ x y → is-decidable (R (F M) x y))
                   → {a : formula i}
                   → ⊢ a
                   → M ⊨M a
  finite-soundness (M , is-fin) dec-val dec-r d =
    soundness d M (finite-is-classical ((M , is-fin)) dec-val dec-r)


double-negation-LEM : {l : Level} → ((A : UU l) → ¬¬ A → A) → LEM l
double-negation-LEM dn A = dn _ λ ndec → ndec (inr (λ a → ndec (inl a)))

lift-dn : {l1 l2 : Level} {A : UU l1} → ¬¬ A → (Lift l2 A → Lift l2 empty) → Lift l2 empty
lift-dn dn nA = lift (dn (λ a → lower (nA (lift a))))

required-LEM : ({l1 l2 l3 : Level} (i : UU l2) (a : formula i)
                → ⊢ a
                → (w : UU l1)
                → (M : kripke-model w i l3)
                → M ⊨M a)
             → {l : Level} → LEM l
required-LEM sound {l} =
  double-negation-LEM λ A nnA → lower (sound unit b ax-dn unit (M A) star (lift-dn nnA))
  where
    a = var star
    b = (~ (~ a)) ⇒ a

    f : kripke-frame unit
    f = frame (λ _ _ → empty) (unit-trunc-Prop star)

    M : UU l → kripke-model unit unit l
    M A = model f (λ _ _ → A)
```
