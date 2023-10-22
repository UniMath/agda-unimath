# Modal logic syntax

```agda
module modal-logic.modal-logic-syntax where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
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
open import foundation.raising-universe-levels
open import foundation.decidable-propositions
open import foundation.law-of-excluded-middle

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.decidable-dependent-function-types
```

</details>

## Idea

TODO

## Definition

**Syntax**

```agda
module _
  {l : Level}
  (i : UU l)
  where

  infixr 4 _⇒_
  infixr 7 □_

  data formula : UU l where
    var : i → formula
    ⊥ : formula
    _⇒_ : formula → formula → formula
    □_ : formula → formula

module _
  {l : Level}
  {i : UU l}
  where

  infixr 7 ~_
  infixr 7 ~~_
  infixr 5 _∨_
  infixr 6 _∧_
  infixr 7 ◇_
  infixr 2 ⊢_

  ~_ : formula i → formula i
  ~ a = a ⇒ ⊥

  ~~_ : formula i → formula i
  ~~ a = ~ ~ a

  _∨_ : formula i → formula i → formula i
  a ∨ b = ~ a ⇒ b

  _∧_ : formula i → formula i → formula i
  a ∧ b = ~ a ⇒ ~ b

  ⊤ : formula i
  ⊤ = ~ ⊥

  ◇_ : formula i → formula i
  ◇ a = ~ □ ~ a

  data ⊢_ : formula i → UU l where
    ax-k : {a b : formula i} → ⊢ a ⇒ b ⇒ a
    ax-s : {a b c : formula i} → ⊢ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
    ax-dn : {a : formula i} → ⊢ ~~ a ⇒ a
    ax-n : {a b : formula i} → ⊢ □ (a ⇒ b) ⇒ □ a ⇒ □ b
    mp : {a b : formula i} → ⊢ a ⇒ b → ⊢ a → ⊢ b
    nec : {a : formula i} → ⊢ a → ⊢ □ a
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
      V : i → w → Prop l3
  open kripke-model public

  finite-model : UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
  finite-model = kripke-model × is-finite w


module _
  {l1 l2 l3 : Level}
  {w : UU l1} {i : UU l2}
  where

  private
    l = l1 ⊔ l2 ⊔ l3

  infix 2 _⊨_
  infix 2 _⊭_
  infix 2 _⊨M_
  infix 2 _⊭M_

  _⊨_ : kripke-model w i l3 × w → formula i → Prop l
  M , x ⊨ var n = raise-Prop l (V M n x)
  M , x ⊨ ⊥ = raise-empty-Prop l
  M , x ⊨ a ⇒ b = hom-Prop (M , x ⊨ a) (M , x ⊨ b)
  M , x ⊨ □ a = Π-Prop w λ y -> function-Prop (R (F M) x y) (M , y ⊨ a)

  _⊭_ : kripke-model w i l3 × w → formula i → Prop l
  M , x ⊭ a = neg-Prop (M , x ⊨ a)

  _⊨M_ : kripke-model w i l3 → formula i → Prop l
  M ⊨M a = Π-Prop w λ x → M , x ⊨ a

  _⊭M_ : kripke-model w i l3 → formula i → Prop l
  M ⊭M a = neg-Prop (M ⊨M a)
```

**Soundness**

```agda
  is-classical-Prop : kripke-model w i l3 → Prop l
  is-classical-Prop M = Π-Prop (formula i) (λ a → Π-Prop w (λ x → is-decidable-Prop (M , x ⊨ a)))

  is-classical : kripke-model w i l3 → UU l
  is-classical = type-Prop ∘ is-classical-Prop

  classical-model : UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
  classical-model = Σ (kripke-model w i l3) is-classical

  soundness : ((M , _) : classical-model)
            → {a : formula i}
            → ⊢ a
            → type-Prop (M ⊨M a)
  soundness _ ax-k x = λ fa _ → fa
  soundness _ ax-s x = λ fabc fab fa → fabc fa (fab fa)
  soundness (_ , cl) {_ ⇒ a} ax-dn x with cl a x
  ... | inl fa = λ _ → fa
  ... | inr nfa = λ fnna → ex-falso (map-inv-raise (fnna (λ fa → map-raise (nfa fa))))
  soundness _ ax-n x = λ fab fa y r → fab y r (fa y r)
  soundness CM (mp dab da) x = soundness CM dab x (soundness CM da x)
  soundness CM (nec d) x y _ = soundness CM d y

  finite-is-classical : ((M , _) : finite-model w i l3)
                      → (∀ n x → type-Prop (is-decidable-Prop (V M n x)))
                      → (∀ x y → is-decidable (R (F M) x y))
                      → is-classical M
  finite-is-classical (M , is-fin) dec-val dec-r (var n) x =
    is-decidable-raise _ _ (dec-val n x)
  finite-is-classical (M , is-fin) dec-val dec-r ⊥ x =
    inr map-inv-raise
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
                   → (∀ n x → type-Prop (is-decidable-Prop (V M n x)))
                   → (∀ x y → is-decidable (R (F M) x y))
                   → {a : formula i}
                   → ⊢ a
                   → type-Prop (M ⊨M a)
  finite-soundness FM@(M , is-fin) dec-val dec-r =
    soundness (M , finite-is-classical FM dec-val dec-r)


double-negation-LEM : {l : Level} → ((P : Prop l) → ¬¬ (type-Prop P) → (type-Prop P)) → LEM l
double-negation-LEM dnP P = dnP (is-decidable-Prop P) (λ ndec → ndec (inr (λ p → ndec (inl p))))

raise-dn : {l1 l2 : Level} {A : UU l1} → ¬¬ A → (raise l2 A → raise-empty l2) → raise-empty l2
raise-dn dnA rnA = map-raise (dnA λ a → map-inv-raise (rnA (map-raise a)))

required-LEM : ({l1 l2 l3 : Level} (w : UU l1) (i : UU l2) (a : formula i)
                (M : kripke-model w i l3)
                → {a : formula i}
                → ⊢ a
                → type-Prop (M ⊨M a))
             → {l : Level} → LEM l
required-LEM sound {l} = double-negation-LEM required-double-negation
  where
    required-double-negation : (P : Prop l) → ¬¬ (type-Prop P) → type-Prop P
    required-double-negation P dnP = map-inv-raise (sound unit unit b (M P) (ax-dn {a = a}) star (raise-dn dnP))
      where

      a = var star
      b = ~~ a ⇒ a

      f : kripke-frame unit
      f = frame (λ _ _ → empty) (unit-trunc-Prop star)

      M : Prop l → kripke-model unit unit l
      M P = model f (λ _ _ → P)
```
