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
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.endomorphisms
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
  iterate-exp-ℕ (succ-ℕ k) l f x =
    ( iterate-mul-ℕ (exp-ℕ l k) l f x) ∙
    ( ( iterate-exp-ℕ k l (iterate l f) x) ∙
      ( inv (htpy-eq (reassociate-iterate-succ-ℕ k (iterate l) f) x)))

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
  (P : subtype l2 (X → X))
  where

  is-in-subtype-iterate-succ-ℕ :
    (F : is-in-subtype P f) →
    ( (h g : X → X) →
      is-in-subtype P h →
      is-in-subtype P g →
      is-in-subtype P (h ∘ g)) →
    (n : ℕ) → is-in-subtype P (iterate (succ-ℕ n) f)
  is-in-subtype-iterate-succ-ℕ F H zero-ℕ = F
  is-in-subtype-iterate-succ-ℕ F H (succ-ℕ n) =
    H f (iterate (succ-ℕ n) f) F (is-in-subtype-iterate-succ-ℕ F H n)

  is-in-subtype-iterate :
    (I : is-in-subtype P (id {A = X})) →
    (F : is-in-subtype P f) →
    ( (h g : X → X) →
      is-in-subtype P h →
      is-in-subtype P g →
      is-in-subtype P (h ∘ g)) →
    (n : ℕ) → is-in-subtype P (iterate n f)
  is-in-subtype-iterate I F H zero-ℕ = I
  is-in-subtype-iterate I F H (succ-ℕ n) =
    H f (iterate n f) F (is-in-subtype-iterate I F H n)
```

## External links

- [Function iteration](https://www.wikidata.org/wiki/Q5254619) on Wikidata
