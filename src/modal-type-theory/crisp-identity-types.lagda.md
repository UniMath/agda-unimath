# Crisp identity types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

We record here some basic facts about
[identity types](foundation-core.identity-types.md) in crisp contexts.

## Properties

```agda
ind-path-crisp :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {@♭ a : A} →
  (C : (@♭ y : A) (p : a ＝ y) → UU l2) →
  C a refl →
  (@♭ y : A) (@♭ p : a ＝ y) → C y p
ind-path-crisp C b _ refl = b

ap-crisp :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {B : UU l2} {@♭ x y : A}
  (f : (@♭ x : A) → B) → @♭ (x ＝ y) → (f x) ＝ (f y)
ap-crisp f refl = refl
```
