# Suspension Loop Space Adjunction

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.suspension-loop-space-adjunction where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions using (_∘_)
open import foundation.identity-types
open import foundation.universe-levels using (Level; UU)


open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspensions-of-types
```

Define the unit of the adjunction

```agda
module _
  {l1 : Level} (X : UU l1) (x0 : X)
  where

  base-susp : suspension X
  base-susp = N-susp

  shift : (type-Ω (suspension X , base-susp)) → (base-susp ＝ S-susp)
  shift l = l ∙ (merid-susp x0)

  shift* : (Ω (suspension X , base-susp)) →* ((base-susp ＝ S-susp) , (merid-susp x0))
  shift* = shift , refl

  unshift : (base-susp ＝ S-susp) → (type-Ω (suspension X , base-susp))
  unshift p = p ∙ inv (merid-susp x0)

  unshift* : ((base-susp ＝ S-susp) , (merid-susp x0)) →* (Ω (suspension X , base-susp))
  unshift* = unshift , right-inv (merid-susp x0)

  is-equiv-shift : is-equiv shift
  is-equiv-shift = is-equiv-concat' base-susp (merid-susp x0)

  merid-susp* : (X , x0) →* ((base-susp ＝ S-susp) , (merid-susp x0))
  merid-susp* = merid-susp , refl

  unit-susp-loop-adj : (X , x0) →* Ω (suspension X , base-susp)
  unit-susp-loop-adj = comp-pointed-map _ _ _ unshift* merid-susp*

  counit-susp-loop-adj : ((suspension (type-Ω (X , x0))) , N-susp) →* (X , x0)
  counit-susp-loop-adj = comp-pointed-map _ _ _ {!up-pushout!} {!!}
```
