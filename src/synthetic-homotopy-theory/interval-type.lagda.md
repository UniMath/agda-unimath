# The interval

```agda
module synthetic-homotopy-theory.interval-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

**The interval type** is a higher inductive type with two points and an
[identification](foundation.identity-types.md) between them.

## Postulates

```agda
postulate

  𝕀 : UU lzero

  source-𝕀 : 𝕀

  target-𝕀 : 𝕀

  path-𝕀 : source-𝕀 ＝ target-𝕀

  ind-𝕀 :
    {l : Level} (P : 𝕀 → UU l) (u : P source-𝕀) (v : P target-𝕀)
    (q : dependent-identification P path-𝕀 u v) → (x : 𝕀) → P x

  compute-source-𝕀 :
    {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀)
    (q : dependent-identification P path-𝕀 u v) → ind-𝕀 P u v q source-𝕀 ＝ u

  compute-target-𝕀 :
    {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀)
    (q : dependent-identification P path-𝕀 u v) → ind-𝕀 P u v q target-𝕀 ＝ v

  compute-path-𝕀 :
    {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀)
    (q : dependent-identification P path-𝕀 u v) →
    coherence-square-identifications
      ( ap (tr P path-𝕀) (compute-source-𝕀 u v q))
      ( apd (ind-𝕀 P u v q) path-𝕀)
      ( q)
      ( compute-target-𝕀 u v q)
```

## Properties

### The data that is used to apply the inductiopn principle of the interval

```agda
Data-𝕀 : {l : Level} → (𝕀 → UU l) → UU l
Data-𝕀 P =
  Σ ( P source-𝕀)
    ( λ u →
      Σ ( P target-𝕀) (dependent-identification P path-𝕀 u))

ev-𝕀 : {l : Level} {P : 𝕀 → UU l} → ((x : 𝕀) → P x) → Data-𝕀 P
ev-𝕀 f = triple (f source-𝕀) (f target-𝕀) (apd f path-𝕀)

module _
  {l : Level} {P : 𝕀 → UU l}
  where

  Eq-Data-𝕀 : (x y : Data-𝕀 P) → UU l
  Eq-Data-𝕀 x y =
    Σ ( pr1 x ＝ pr1 y)
      ( λ α →
        Σ ( pr1 (pr2 x) ＝ pr1 (pr2 y))
          ( λ β →
            coherence-square-identifications
              ( ap (tr P path-𝕀) α)
              ( pr2 (pr2 x))
              ( pr2 (pr2 y))
              ( β)))

  extensionality-Data-𝕀 : (x y : Data-𝕀 P) → (x ＝ y) ≃ Eq-Data-𝕀 x y
  extensionality-Data-𝕀 (pair u (pair v α)) =
    extensionality-Σ
      ( λ {u'} vα' p →
        Σ ( v ＝ pr1 vα')
          ( λ q →
            coherence-square-identifications
              ( ap (tr P path-𝕀) p)
              ( α)
              ( pr2 vα')
              ( q)))
      ( refl)
      ( pair refl right-unit)
      ( λ u' → id-equiv)
      ( extensionality-Σ
        ( λ {v'} α' q → α ∙ q ＝ α')
        ( refl)
        ( right-unit)
        ( λ v' → id-equiv)
        ( λ γ → equiv-concat right-unit γ))

  refl-Eq-Data-𝕀 : (x : Data-𝕀 P) → Eq-Data-𝕀 x x
  refl-Eq-Data-𝕀 x = triple refl refl right-unit

  Eq-eq-Data-𝕀 : {x y : Data-𝕀 P} → x ＝ y → Eq-Data-𝕀 x y
  Eq-eq-Data-𝕀 {x = x} refl = refl-Eq-Data-𝕀 x

  eq-Eq-Data-𝕀' : {x y : Data-𝕀 P} → Eq-Data-𝕀 x y → x ＝ y
  eq-Eq-Data-𝕀' {x} {y} = map-inv-equiv (extensionality-Data-𝕀 x y)

  eq-Eq-Data-𝕀 :
    {x y : Data-𝕀 P} (α : pr1 x ＝ pr1 y) (β : pr1 (pr2 x) ＝ pr1 (pr2 y))
    (γ :
      coherence-square-identifications
        ( ap (tr P path-𝕀) α)
        ( pr2 (pr2 x))
        ( pr2 (pr2 y))
        ( β)) →
    x ＝ y
  eq-Eq-Data-𝕀 α β γ = eq-Eq-Data-𝕀' (triple α β γ)
```

### The interval is contractible

```agda
inv-ev-𝕀 : {l : Level} {P : 𝕀 → UU l} → Data-𝕀 P → (x : 𝕀) → P x
inv-ev-𝕀 x = ind-𝕀 _ (pr1 x) (pr1 (pr2 x)) (pr2 (pr2 x))

is-section-inv-ev-𝕀 :
  {l : Level} {P : 𝕀 → UU l} (x : Data-𝕀 P) → ev-𝕀 (inv-ev-𝕀 x) ＝ x
is-section-inv-ev-𝕀 (pair u (pair v q)) =
  eq-Eq-Data-𝕀
    ( compute-source-𝕀 u v q)
    ( compute-target-𝕀 u v q)
    ( compute-path-𝕀 u v q)

tr-value :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x) {x y : A}
  (p : x ＝ y) (q : f x ＝ g x) (r : f y ＝ g y) →
  apd f p ∙ r ＝ ap (tr B p) q ∙ apd g p →
  tr (λ x → f x ＝ g x) p q ＝ r
tr-value f g refl q r s = (inv (ap-id q) ∙ inv right-unit) ∙ inv s

is-retraction-inv-ev-𝕀 :
  {l : Level} {P : 𝕀 → UU l} (f : (x : 𝕀) → P x) → Id (inv-ev-𝕀 (ev-𝕀 f)) f
is-retraction-inv-ev-𝕀 {l} {P} f =
  eq-htpy
    ( ind-𝕀
      ( eq-value (inv-ev-𝕀 (ev-𝕀 f)) f)
      ( compute-source-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))
      ( compute-target-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))
      ( map-compute-dependent-identification-eq-value
        ( inv-ev-𝕀 (ev-𝕀 f))
        ( f)
        ( path-𝕀)
        ( compute-source-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))
        ( compute-target-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))
        ( compute-path-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))))

abstract
  is-equiv-ev-𝕀 :
    {l : Level} (P : 𝕀 → UU l) → is-equiv (ev-𝕀 {P = P})
  is-equiv-ev-𝕀 P =
    is-equiv-is-invertible inv-ev-𝕀 is-section-inv-ev-𝕀 is-retraction-inv-ev-𝕀

contraction-𝕀 : (x : 𝕀) → source-𝕀 ＝ x
contraction-𝕀 =
  ind-𝕀
    ( Id source-𝕀)
    ( refl)
    ( path-𝕀)
    ( tr-Id-right path-𝕀 refl)

abstract
  is-contr-𝕀 : is-contr 𝕀
  pr1 is-contr-𝕀 = source-𝕀
  pr2 is-contr-𝕀 = contraction-𝕀
```
