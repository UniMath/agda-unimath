# Iterating functions

```agda
module foundation.iterating-functions where

open import foundation-core.iterating-functions public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplicative-monoid-of-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.propositional-maps
open import foundation.subtypes
open import foundation.truncated-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.endomorphisms
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.monoid-actions
```

</details>

## Idea

Any map `f : X → X` can be
{{#concept "iterated" Disambiguation="endo map of types"}} by repeatedly
applying `f`.

## Properties

### For any map `f : X → X`, iterating `f` defines a monoid action of ℕ on `X`

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-add-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (k +ℕ l) f x ＝ iterate k f (iterate l f x)
  iterate-add-ℕ k zero-ℕ f x = refl
  iterate-add-ℕ k (succ-ℕ l) f x =
    ap f (iterate-add-ℕ k l f x) ∙
    reassociate-iterate-succ-ℕ k f (iterate l f x)

  left-unit-law-iterate-add-ℕ :
    (l : ℕ) (f : X → X) (x : X) →
    iterate-add-ℕ 0 l f x ＝ ap (λ t → iterate t f x) (left-unit-law-add-ℕ l)
  left-unit-law-iterate-add-ℕ zero-ℕ f x = refl
  left-unit-law-iterate-add-ℕ (succ-ℕ l) f x =
    ( right-unit) ∙
    ( ( ap² f (left-unit-law-iterate-add-ℕ l f x)) ∙
      ( ( inv (ap-comp f (λ t → iterate t f x) (left-unit-law-add-ℕ l))) ∙
        ( ap-comp (λ t → iterate t f x) succ-ℕ (left-unit-law-add-ℕ l))))

  right-unit-law-iterate-add-ℕ :
    (k : ℕ) (f : X → X) (x : X) →
    iterate-add-ℕ k 0 f x ＝ ap (λ t → iterate t f x) (right-unit-law-add-ℕ k)
  right-unit-law-iterate-add-ℕ k f x = refl

  iterate-iterate :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate k f (iterate l f x) ＝ iterate l f (iterate k f x)
  iterate-iterate k l f x =
    ( inv (iterate-add-ℕ k l f x)) ∙
    ( ( ap (λ t → iterate t f x) (commutative-add-ℕ k l)) ∙
      ( iterate-add-ℕ l k f x))

  iterate-mul-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (k *ℕ l) f x ＝ iterate k (iterate l f) x
  iterate-mul-ℕ zero-ℕ l f x = refl
  iterate-mul-ℕ (succ-ℕ k) l f x =
    ( iterate-add-ℕ (k *ℕ l) l f x) ∙
    ( ( iterate-mul-ℕ k l f (iterate l f x)) ∙
      ( inv (reassociate-iterate-succ-ℕ k (iterate l f) x)))

  iterate-exp-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (exp-ℕ l k) f x ＝ iterate k (iterate l) f x
  iterate-exp-ℕ zero-ℕ l f x = refl
  iterate-exp-ℕ (succ-ℕ zero-ℕ) l f x = refl
  iterate-exp-ℕ (succ-ℕ (succ-ℕ k)) l f x =
    ( iterate-mul-ℕ (exp-ℕ l (succ-ℕ k)) l f x) ∙
    ( ( iterate-exp-ℕ (succ-ℕ k) l (iterate l f) x) ∙
      ( inv (htpy-eq (reassociate-iterate-succ-ℕ (succ-ℕ k) (iterate l) f) x)))

module _
  {l : Level} (X : Set l)
  where

  iterative-action-Monoid : action-Monoid l ℕ*-Monoid
  pr1 iterative-action-Monoid = endo-Set X
  pr1 (pr1 (pr2 iterative-action-Monoid)) k f = iterate k f
  pr2 (pr1 (pr2 iterative-action-Monoid)) {k} {l} =
    eq-htpy (λ f → eq-htpy (λ x → iterate-mul-ℕ k l f x))
  pr2 (pr2 iterative-action-Monoid) = refl
```

### If `f : X → X` satisfies a property of endofunctions on `X`, and the property is closed under composition then iterates of `f` satisfy the property

```agda
module _
  {l1 l2 : Level} {X : UU l1} {f : X → X}
  {P : (X → X) → UU l2}
  where

  is-in-function-class-iterate-succ-ℕ :
    ( (h g : X → X) → P h → P g → P (h ∘ g)) →
    (n : ℕ) → (F : P f) → P (iterate (succ-ℕ n) f)
  is-in-function-class-iterate-succ-ℕ H zero-ℕ F = F
  is-in-function-class-iterate-succ-ℕ H (succ-ℕ n) F =
    H f (iterate (succ-ℕ n) f) F (is-in-function-class-iterate-succ-ℕ H n F)

  is-in-function-class-iterate :
    (I : P (id {A = X})) →
    ((h g : X → X) → P h → P g → P (h ∘ g)) →
    (n : ℕ) → (F : P f) → P (iterate n f)
  is-in-function-class-iterate I H zero-ℕ F = I
  is-in-function-class-iterate I H (succ-ℕ n) F =
    H f (iterate n f) F (is-in-function-class-iterate I H n F)
```

### Iterates of equivalences are equivalences

```agda
module _
  {l : Level} {X : UU l} {f : X → X}
  where

  abstract
    is-equiv-iterate : (n : ℕ) → is-equiv f → is-equiv (iterate n f)
    is-equiv-iterate =
      is-in-function-class-iterate is-equiv-id
        ( λ h g H G → is-equiv-comp h g G H)
```

### Iterates of embeddings are embeddings

```agda
module _
  {l : Level} {X : UU l} {f : X → X}
  where

  abstract
    is-emb-iterate : (n : ℕ) → is-emb f → is-emb (iterate n f)
    is-emb-iterate = is-in-function-class-iterate is-emb-id is-emb-comp
```

### Iterates of truncated maps are truncated

```agda
module _
  {l : Level} (k : 𝕋) {X : UU l} {f : X → X}
  where

  abstract
    is-trunc-map-iterate :
      (n : ℕ) → is-trunc-map k f → is-trunc-map k (iterate n f)
    is-trunc-map-iterate =
      is-in-function-class-iterate (is-trunc-map-id k) (is-trunc-map-comp k)
```

### Iterates of propositional maps are propositional

```agda
module _
  {l : Level} (k : 𝕋) {X : UU l} {f : X → X}
  where

  abstract
    is-prop-map-iterate :
      (n : ℕ) → is-prop-map f → is-prop-map (iterate n f)
    is-prop-map-iterate =
      is-in-function-class-iterate is-prop-map-id is-prop-map-comp
```

## External links

- [Function iteration](https://www.wikidata.org/wiki/Q5254619) on Wikidata
