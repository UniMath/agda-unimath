# Binary relations

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.binary-relations where

open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)
```

## Definition

A binary relation of universe level `l` is a map `R : A → A → UU l`.

```agda
Rel : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
Rel l A = A → A → UU l
```

## Specifications of properties of binary relations

```agda
is-reflexive : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-reflexive {A = A} R = (x : A) → R x x

is-symmetric : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-symmetric {A = A} R = (x y : A) → R x y → R y x

is-transitive : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-transitive {A = A} R = (x y z : A) → R x y → R y z → R x z
```
