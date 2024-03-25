# Modal logic formulas

```agda
module modal-logic.formulas where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l : Level} (i : Set l)
  where

  infixr 7 _→ₘ_
  infixr 25 □_

  data formula : UU l where
    var : type-Set i → formula
    ⊥ : formula
    _→ₘ_ : formula → formula → formula
    □_ : formula → formula

module _
  {l : Level} {i : Set l}
  where

  infixr 25 ~_
  infixr 25 ~~_
  -- infixl 10 _∨_
  -- infixl 15 _∧_
  infixr 25 ◇_

  ~_ : formula i → formula i
  ~ a = a →ₘ ⊥

  ~~_ : formula i → formula i
  ~~ a = ~ ~ a

  -- _∨_ : formula i → formula i → formula i
  -- a ∨ b = ~ a →ₘ b

  -- _∧_ : formula i → formula i → formula i
  -- a ∧ b = ~ (a →ₘ ~ b)

  ⊤ : formula i
  ⊤ = ~ ⊥

  ◇_ : formula i → formula i
  ◇ a = ~ □ ~ a

  eq-implication-left : {a b c d : formula i} → a →ₘ b ＝ c →ₘ d → a ＝ c
  eq-implication-left refl = refl

  eq-implication-right : {a b c d : formula i} → a →ₘ b ＝ c →ₘ d → b ＝ d
  eq-implication-right refl = refl

  eq-box : {a b : formula i} → □ a ＝ □ b → a ＝ b
  eq-box refl = refl

  eq-diamond : {a b : formula i} → ◇ a ＝ ◇ b → a ＝ b
  eq-diamond refl = refl
```

## Properties

### The formulas are a set

```agda
module _
  {l : Level} (i : Set l)
  where

  Eq-formula : formula i → formula i → UU l
  Eq-formula (var n) (var m) = n ＝ m
  Eq-formula (var _) ⊥ = raise-empty l
  Eq-formula (var _) (_ →ₘ _) = raise-empty l
  Eq-formula (var -) (□ _) = raise-empty l
  Eq-formula ⊥ (var _) = raise-empty l
  Eq-formula ⊥ ⊥ = raise-unit l
  Eq-formula ⊥ (_ →ₘ _) = raise-empty l
  Eq-formula ⊥ (□ _) = raise-empty l
  Eq-formula (_ →ₘ _) (var _) = raise-empty l
  Eq-formula (_ →ₘ _) ⊥ = raise-empty l
  Eq-formula (a →ₘ b) (c →ₘ d) = (Eq-formula a c) × (Eq-formula b d)
  Eq-formula (_ →ₘ _) (□ _) = raise-empty l
  Eq-formula (□ _) (var _) = raise-empty l
  Eq-formula (□ _) ⊥ = raise-empty l
  Eq-formula (□ _) (_ →ₘ _) = raise-empty l
  Eq-formula (□ a) (□ c) = Eq-formula a c

  refl-Eq-formula : (a : formula i) → Eq-formula a a
  refl-Eq-formula (var n) = refl
  refl-Eq-formula ⊥ = raise-star
  refl-Eq-formula (a →ₘ b) = (refl-Eq-formula a) , (refl-Eq-formula b)
  refl-Eq-formula (□ a) = refl-Eq-formula a

  Eq-eq-formula : {a b : formula i} → a ＝ b → Eq-formula a b
  Eq-eq-formula {a} refl = refl-Eq-formula a

  eq-Eq-formula : {a b : formula i} → Eq-formula a b → a ＝ b
  eq-Eq-formula {var _} {var _} refl = refl
  eq-Eq-formula {var _} {⊥} (map-raise ())
  eq-Eq-formula {var _} {_ →ₘ _} (map-raise ())
  eq-Eq-formula {var _} {□ _} (map-raise ())
  eq-Eq-formula {⊥} {var _} (map-raise ())
  eq-Eq-formula {⊥} {⊥} _ = refl
  eq-Eq-formula {⊥} {_ →ₘ _} (map-raise ())
  eq-Eq-formula {⊥} {□ _} (map-raise ())
  eq-Eq-formula {_ →ₘ _} {var _} (map-raise ())
  eq-Eq-formula {_ →ₘ _} {⊥} (map-raise ())
  eq-Eq-formula {a →ₘ b} {c →ₘ d} (eq1 , eq2) =
    ap (λ (x , y) → x →ₘ y) (eq-pair (eq-Eq-formula eq1) (eq-Eq-formula eq2))
  eq-Eq-formula {_ →ₘ _} {□ _} (map-raise ())
  eq-Eq-formula {□ _} {var _} (map-raise ())
  eq-Eq-formula {□ _} {⊥} (map-raise ())
  eq-Eq-formula {□ _} {_ →ₘ _} (map-raise ())
  eq-Eq-formula {□ _} {□ _} eq = ap □_ (eq-Eq-formula eq)

  is-prop-Eq-formula : (a b : formula i) → is-prop (Eq-formula a b)
  is-prop-Eq-formula (var n) (var m) = is-prop-type-Prop (Id-Prop i n m)
  is-prop-Eq-formula (var _) ⊥ = is-prop-raise-empty
  is-prop-Eq-formula (var _) (_ →ₘ _) = is-prop-raise-empty
  is-prop-Eq-formula (var -) (□ _) = is-prop-raise-empty
  is-prop-Eq-formula ⊥ (var _) = is-prop-raise-empty
  is-prop-Eq-formula ⊥ ⊥ = is-prop-raise-unit
  is-prop-Eq-formula ⊥ (_ →ₘ _) = is-prop-raise-empty
  is-prop-Eq-formula ⊥ (□ _) = is-prop-raise-empty
  is-prop-Eq-formula (_ →ₘ _) (var _) = is-prop-raise-empty
  is-prop-Eq-formula (_ →ₘ _) ⊥ = is-prop-raise-empty
  is-prop-Eq-formula (a →ₘ b) (c →ₘ d) =
    is-prop-product (is-prop-Eq-formula a c) (is-prop-Eq-formula b d)
  is-prop-Eq-formula (_ →ₘ _) (□ _) = is-prop-raise-empty
  is-prop-Eq-formula (□ _) (var _) = is-prop-raise-empty
  is-prop-Eq-formula (□ _) ⊥ = is-prop-raise-empty
  is-prop-Eq-formula (□ _) (_ →ₘ _) = is-prop-raise-empty
  is-prop-Eq-formula (□ a) (□ c) = is-prop-Eq-formula a c

  is-set-formula : is-set (formula i)
  is-set-formula =
    is-set-prop-in-id
      ( Eq-formula)
      ( is-prop-Eq-formula)
      ( refl-Eq-formula)
      ( λ _ _ → eq-Eq-formula)

  formula-Set : Set l
  pr1 formula-Set = formula i
  pr2 formula-Set = is-set-formula

Id-formula-Prop : {l : Level} {i : Set l} → formula i → formula i → Prop l
Id-formula-Prop = Id-Prop (formula-Set _)
```
