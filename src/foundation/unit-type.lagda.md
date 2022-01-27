---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.unit-type where

open import foundation.contractible-types using
  ( is-contr; center; contraction)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.functions using (const; _∘_; id)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.identity-types using (Id; refl)
open import foundation.universe-levels using (Level; lzero; UU)
open import foundation.propositions using (is-prop; is-prop-is-contr; UU-Prop)
open import foundation.raising-universe-levels using
  ( raise; equiv-raise; map-raise)
```

## The unit type

```agda
data unit : UU lzero where
  star : unit

ind-unit : {l : Level} {P : unit → UU l} → P star → ((x : unit) → P x)
ind-unit p star = p

terminal-map : {l : Level} {A : UU l} → A → unit
terminal-map a = star
```

```agda
abstract
  is-contr-unit : is-contr unit
  pr1 is-contr-unit = star
  pr2 is-contr-unit star = refl
```

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-equiv-terminal-map-is-contr :
      is-contr A → is-equiv (terminal-map {A = A})
    pr1 (pr1 (is-equiv-terminal-map-is-contr H)) = ind-unit (center H)
    pr2 (pr1 (is-equiv-terminal-map-is-contr H)) = ind-unit refl
    pr1 (pr2 (is-equiv-terminal-map-is-contr H)) = const unit A (center H)
    pr2 (pr2 (is-equiv-terminal-map-is-contr H)) = contraction H

  abstract
    is-contr-is-equiv-const : is-equiv (terminal-map {A = A}) → is-contr A
    pr1 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = h star
    pr2 (is-contr-is-equiv-const (pair (pair g issec) (pair h isretr))) = isretr
```

```agda
abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : UU-Prop lzero
pr1 unit-Prop = unit
pr2 unit-Prop = is-prop-unit
```

```agda
raise-unit : (l : Level) → UU l
raise-unit l = raise l unit

raise-star : {l : Level} → raise l unit
raise-star = map-raise star

equiv-raise-unit : (l : Level) → unit ≃ raise-unit l
equiv-raise-unit l = equiv-raise l unit
```
