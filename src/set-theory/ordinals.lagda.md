# Ordinals

```agda
module set-theory.ordinals where
```
 
<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.contractible-types
```


## Definition

```agda
bin-rel : {l : Level} → UU l → UU (lsuc l)
bin-rel {l} A = A → A → Prop l

module _
  {l : Level} {A : UU l} (_<_ : bin-rel A)
  where

  data acc (a : A) : UU l where
    instance acc< : ((b : A) → pr1 (b < a) → acc b) → acc a

  ind-acc : (P : (a : A) → acc a → UU l) →
              ((a : A) → (h : (b : A) → pr1 (b < a) → acc b) →
              ((b : A) → (l : pr1 (b < a)) → P b (h b l))
              → P a (acc< h))
            → ((a : A) → (c : acc a) → P a c)
  ind-acc P f = g
    where
    g : (a : A) → (c : acc a) → P a c
    g a (acc< h) = f a h (λ b k → g b (h b k))

  is-prop-acc : (a : A) → is-contr (acc a)
  is-prop-acc a = ind-acc {!!} {!!} {!!} {!!}
  ```
