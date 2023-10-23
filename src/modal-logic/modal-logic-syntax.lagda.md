# Modal logic syntax

```agda
module modal-logic.modal-logic-syntax where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

TODO

## Definition

### Syntax

```agda
module _
  {l : Level} (i : UU l)
  where

  infixr 6 _⇒_
  infixr 25 □_

  data formula : UU l where
    var : i → formula
    ⊥ : formula
    _⇒_ : formula → formula → formula
    □_ : formula → formula

module _
  {l : Level} {i : UU l}
  where

  infixr 25 ~_
  infixr 25 ~~_
  infixl 10 _∨_
  infixl 15 _∧_
  infixr 25 ◇_
  infix 5 ⊢_

  ~_ : formula i → formula i
  ~ a = a ⇒ ⊥

  ~~_ : formula i → formula i
  ~~ a = ~ ~ a

  _∨_ : formula i → formula i → formula i
  a ∨ b = ~ a ⇒ b

  _∧_ : formula i → formula i → formula i
  a ∧ b = ~ (a ⇒ ~ b)

  ⊤ : formula i
  ⊤ = ~ ⊥

  ◇_ : formula i → formula i
  ◇ a = ~ □ ~ a

  data ⊢_ : formula i → UU l where
    ax-k : (a b : formula i) → ⊢ a ⇒ b ⇒ a
    ax-s : (a b c : formula i) → ⊢ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
    ax-dn : (a : formula i) → ⊢ ~~ a ⇒ a
    ax-n : (a b : formula i) → ⊢ □ (a ⇒ b) ⇒ □ a ⇒ □ b
    mp : {a b : formula i} → ⊢ a ⇒ b → ⊢ a → ⊢ b
    nec : {a : formula i} → ⊢ a → ⊢ □ a
```

### Semantics

```agda
module _
  {l1 : Level} ((w , _) : Inhabited-Type l1) (l2 : Level)
  where

  record kripke-frame : UU (l1 ⊔ lsuc l2) where
    constructor frame
    field
      frame-relation : Relation l2 w
  open kripke-frame public

module _
  {l1 : Level} (W@(w , _) : Inhabited-Type l1)
  (l2 : Level)
  {l3 : Level} (i : UU l3)
  (l4 : Level)
  where

  record kripke-model : UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4) where
    constructor model
    field
      model-frame : kripke-frame W l2
      model-valuate : i → w → Prop l4
  open kripke-model public

  finite-model : UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4)
  finite-model = kripke-model × is-finite w

module _
  {l1 l2 l3 l4 : Level} {W@(w , _) : Inhabited-Type l1} {i : UU l3}
  where

  model-relation : kripke-model W l2 i l4 → Relation l2 w
  model-relation = frame-relation ∘ model-frame

  private
    l = l1 ⊔ l2 ⊔ l4

  infix 5 _⊨_
  infix 5 _⊭_
  infix 5 _⊨M_
  infix 5 _⊭M_

  _⊨_ : kripke-model W l2 i l4 × w → formula i → Prop l
  (M , x) ⊨ var n = raise-Prop l (model-valuate M n x)
  (M , x) ⊨ ⊥ = raise-empty-Prop l
  (M , x) ⊨ a ⇒ b = hom-Prop ((M , x) ⊨ a) ((M , x) ⊨ b)
  (M , x) ⊨ □ a =
    Π-Prop w (λ y -> function-Prop (model-relation M x y) ((M , y) ⊨ a))

  _⊭_ : kripke-model W l2 i l4 × w → formula i → Prop l
  (M , x) ⊭ a = neg-Prop ((M , x) ⊨ a)

  _⊨M_ : kripke-model W l2 i l4 → formula i → Prop l
  M ⊨M a = Π-Prop w (λ x → (M , x) ⊨ a)

  _⊭M_ : kripke-model W l2 i l4 → formula i → Prop l
  M ⊭M a = neg-Prop (M ⊨M a)
```

### Soundness

```agda
module _
  {l1 l2 l3 l4 : Level} {W@(w , _) : Inhabited-Type l1} {i : UU l3}
  where

  private
    l = l1 ⊔ l2 ⊔ l3 ⊔ l4

  is-classical-Prop : kripke-model W l2 i l4 → Prop l
  is-classical-Prop M =
    Π-Prop (formula i) (λ a → Π-Prop w (λ x → is-decidable-Prop ((M , x) ⊨ a)))

  is-classical : kripke-model W l2 i l4 → UU l
  is-classical = type-Prop ∘ is-classical-Prop

  classical-model : UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4)
  classical-model = Σ (kripke-model W l2 i l4) is-classical

  soundness :
    ((M , _) : classical-model)
    {a : formula i} →
    ⊢ a →
    type-Prop (M ⊨M a)
  soundness _ (ax-k _ _) x fa _ = fa
  soundness _ (ax-s _ _ _) x fabc fab fa = fabc fa (fab fa)
  soundness (_ , cl) (ax-dn a) x fdna with cl a x
  ... | inl fa = fa
  ... | inr nfa = ex-falso (map-inv-raise (fdna (λ fa → map-raise (nfa fa))))
  soundness _ (ax-n _ _) x fab fa y r = fab y r (fa y r)
  soundness CM (mp dab da) x = soundness CM dab x (soundness CM da x)
  soundness CM (nec d) x y _ = soundness CM d y

  module _
    ((M , w-is-finite) : finite-model W l2 i l4)
    (dec-val : ∀ n x → type-Prop (is-decidable-Prop (model-valuate M n x)))
    (dec-r : ∀ x y → is-decidable (model-relation M x y))
    where

    finite-is-classical : is-classical M
    finite-is-classical (var n) x =
      is-decidable-raise _ _ (dec-val n x)
    finite-is-classical ⊥ x =
      inr map-inv-raise
    finite-is-classical (a ⇒ b) x =
      is-decidable-function-type
        ( finite-is-classical a x)
        ( finite-is-classical b x)
    finite-is-classical (□ a) x =
      is-decidable-Π-is-finite w-is-finite
        ( λ y →
          is-decidable-function-type (dec-r x y)
          ( finite-is-classical a y))

    finite-soundness : {a : formula i} → ⊢ a → type-Prop (M ⊨M a)
    finite-soundness = soundness (M , finite-is-classical)

double-negation-LEM :
  {l : Level} →
  ((P : Prop l) →
  ¬¬ (type-Prop P) →
  (type-Prop P)) →
  LEM l
double-negation-LEM dnP P =
  dnP (is-decidable-Prop P) (λ ndec → ndec (inr (λ p → ndec (inl p))))

raise-dn :
  {l1 l2 : Level}
  {A : UU l1} →
  ¬¬ A →
  (raise l2 A → raise-empty l2) → raise-empty l2
raise-dn dnA rnA = map-raise (dnA (λ a → map-inv-raise (rnA (map-raise a))))

full-soundness : UUω
full-soundness =
  {l1 l2 l3 l4 : Level}
  (W : Inhabited-Type l1)
  {i : UU l3}
  (M : kripke-model W l2 i l4)
  {a : formula i} →
  ⊢ a →
  type-Prop (M ⊨M a)

full-soundness-required-LEM :
  full-soundness →
  (l : Level) →
  LEM l
full-soundness-required-LEM sound l =
  double-negation-LEM required-double-negation
  where
  required-double-negation : (P : Prop l) → ¬¬ (type-Prop P) → type-Prop P
  required-double-negation P dnP =
    map-inv-raise
      ( sound
        ( unit , unit-trunc-Prop star)
        ( model
          ( frame (λ _ _ → empty))
          ( λ _ _ → P))
        ( ax-dn (var star))
        star
        ( raise-dn dnP))
```
