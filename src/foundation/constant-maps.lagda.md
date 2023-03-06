# Constant maps

<details><summary>Imports</summary>
```agda
module foundation.constant-maps where
open import foundation-core.constant-maps public
open import foundation-core.0-maps
open import foundation-core.1-types
open import foundation-core.contractible-maps
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.faithful-maps
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels
open import foundation.embeddings
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
```
</details>

## Properties

### A type is (k+1)-truncated if and only if all constant maps into it are k-truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  fib-const : (x y : A) → fib (const unit A x) y ≃ (x ＝ y)
  fib-const x y = left-unit-law-prod

  abstract
    is-trunc-map-const-is-trunc :
      (k : 𝕋) → is-trunc (succ-𝕋 k) A →
      (x : A) → is-trunc-map k (const unit A x)
    is-trunc-map-const-is-trunc k is-trunc-A x y =
      is-trunc-equiv k
        ( x ＝ y)
        ( fib-const x y)
        ( is-trunc-A x y)

  abstract
    is-contr-map-const-is-prop :
      is-prop A → (x : A) → is-contr-map (const unit A x)
    is-contr-map-const-is-prop = is-trunc-map-const-is-trunc neg-two-𝕋

  abstract
    is-equiv-const-is-prop :
      is-prop A → (x : A) → is-equiv (const unit A x)
    is-equiv-const-is-prop H x =
      is-equiv-is-contr-map (is-contr-map-const-is-prop H x)

  abstract
    is-prop-map-const-is-set :
      is-set A → (x : A) → is-prop-map (const unit A x)
    is-prop-map-const-is-set = is-trunc-map-const-is-trunc neg-one-𝕋

  abstract
    is-emb-const-is-set : is-set A → (x : A) → is-emb (const unit A x)
    is-emb-const-is-set H x = is-emb-is-prop-map (is-prop-map-const-is-set H x)

  abstract
    is-0-map-const-is-1-type : is-1-type A → (x : A) → is-0-map (const unit A x)
    is-0-map-const-is-1-type = is-trunc-map-const-is-trunc zero-𝕋

  abstract
    is-faithful-const-is-1-type :
      is-1-type A → (x : A) → is-faithful (const unit A x)
    is-faithful-const-is-1-type H x =
      is-faithful-is-0-map (is-0-map-const-is-1-type H x)

  abstract
    is-trunc-is-trunc-map-const :
      (k : 𝕋) → ((x : A) → is-trunc-map k (const unit A x)) →
      is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-const k is-trunc-const x y =
      is-trunc-equiv' k
        ( Σ unit (λ _ → x ＝ y))
        ( left-unit-law-Σ (λ _ → x ＝ y))
        ( is-trunc-const x y)

  abstract
    is-prop-is-contr-map-const :
      ((x : A) → is-contr-map (const unit A x)) → is-prop A
    is-prop-is-contr-map-const = is-trunc-is-trunc-map-const neg-two-𝕋

  abstract
    is-prop-is-equiv-const :
      ((x : A) → is-equiv (const unit A x)) → is-prop A
    is-prop-is-equiv-const H =
      is-prop-is-contr-map-const (λ x → is-contr-map-is-equiv (H x))

  abstract
    is-set-is-prop-map-const :
      ((x : A) → is-prop-map (const unit A x)) → is-set A
    is-set-is-prop-map-const = is-trunc-is-trunc-map-const neg-one-𝕋

  abstract
    is-set-is-emb-const :
      ((x : A) → is-emb (const unit A x)) → is-set A
    is-set-is-emb-const H =
      is-set-is-prop-map-const (λ x → is-prop-map-is-emb (H x))

  abstract
    is-1-type-is-0-map-const :
      ((x : A) → is-0-map (const unit A x)) → is-1-type A
    is-1-type-is-0-map-const = is-trunc-is-trunc-map-const zero-𝕋

  abstract
    is-1-type-is-faithful-const :
      ((x : A) → is-faithful (const unit A x)) → is-1-type A
    is-1-type-is-faithful-const H =
      is-1-type-is-0-map-const (λ x → is-0-map-is-faithful (H x))

const-equiv :
  {l : Level} (A : Prop l) (x : type-Prop A) → unit ≃ type-Prop A
pr1 (const-equiv A x) = const unit (type-Prop A) x
pr2 (const-equiv A x) = is-equiv-const-is-prop (is-prop-type-Prop A) x

const-emb :
  {l : Level} (A : Set l) (x : type-Set A) → unit ↪ type-Set A
pr1 (const-emb A x) = const unit (type-Set A) x
pr2 (const-emb A x) = is-emb-const-is-set (is-set-type-Set A) x

const-faithful-map :
  {l : Level} (A : 1-Type l) (x : type-1-Type A) →
  faithful-map unit (type-1-Type A)
pr1 (const-faithful-map A x) = const unit (type-1-Type A) x
pr2 (const-faithful-map A x) =
  is-faithful-const-is-1-type (is-1-type-type-1-Type A) x
```
