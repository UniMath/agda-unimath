# Asymptotical dependent sequences

```agda
module foundation.asymptotical-dependent-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-sequences
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A dependent sequence `A : ℕ → UU l` is **asymptotical** if `A n` is pointed for
sufficiently large natural numbers `n`.

## Definitions

### Asymptotical dependent sequences

```agda
module _
  {l : Level} (A : ℕ → UU l)
  where

  is-modulus-dependent-sequence : ℕ → UU l
  is-modulus-dependent-sequence N = (n : ℕ) → leq-ℕ N n → A n

  asymptotically : UU l
  asymptotically = Σ ℕ is-modulus-dependent-sequence
```

### Modulus of an asymptotical dependent sequence

```agda
module _
  {l : Level} {A : ℕ → UU l} (H : asymptotically A)
  where

  modulus-∞-asymptotically : ℕ
  modulus-∞-asymptotically = pr1 H

  is-modulus-∞-asymptotically :
    is-modulus-dependent-sequence A modulus-∞-asymptotically
  is-modulus-∞-asymptotically = pr2 H

  value-∞-asymptotically : A modulus-∞-asymptotically
  value-∞-asymptotically =
    is-modulus-∞-asymptotically
      ( modulus-∞-asymptotically)
      ( refl-leq-ℕ modulus-∞-asymptotically)
```

## Properties

### Pointed dependent sequences are asymptotical

```agda
module _
  {l : Level} {A : ℕ → UU l}
  where

  asymptotically-Π : ((n : ℕ) → A n) → asymptotically A
  asymptotically-Π u = (zero-ℕ , λ p I → u p)
```

### Any natural number greater than an asymptotical modulus is an asymptotical modulus

```agda
module _
  {l : Level} (A : ℕ → UU l) (i j : ℕ) (I : leq-ℕ i j)
  where

  is-increasing-is-modulus-dependent-sequence :
    (is-modulus-dependent-sequence A i) → (is-modulus-dependent-sequence A j)
  is-increasing-is-modulus-dependent-sequence H k K =
    H k (transitive-leq-ℕ i j k K I)
```

### A dependent sequence that asymptotically has an asymptotical modulus is asymptotical

```agda
module _
  {l : Level} (A : ℕ → UU l)
  where

  asymptotically-is-modulus-dependent-sequence :
    asymptotically (is-modulus-dependent-sequence A) →
    asymptotically A
  asymptotically-is-modulus-dependent-sequence (N , H) =
    (N , (λ n K → H n K n (refl-leq-ℕ n)))
```

### Asymptotical functorial action on asymptotical dependent sequences

```agda
module _
  {l1 l2 : Level} {A : ℕ → UU l1} {B : ℕ → UU l2}
  where

  map-asymptotically :
    asymptotically (λ n → A n → B n) →
    asymptotically A →
    asymptotically B
  map-asymptotically H K =
    ( max-ℕ (modulus-∞-asymptotically H) (modulus-∞-asymptotically K)) ,
    ( λ q I →
      is-modulus-∞-asymptotically H q
        ( leq-left-leq-max-ℕ q
          ( modulus-∞-asymptotically H)
          ( modulus-∞-asymptotically K)
          ( I))
        ( is-modulus-∞-asymptotically K q
          ( leq-right-leq-max-ℕ q
            ( modulus-∞-asymptotically H)
            ( modulus-∞-asymptotically K)
            ( I))))

  map-asymptotically-Π :
    ((n : ℕ) → A n → B n) →
    asymptotically A →
    asymptotically B
  map-asymptotically-Π H = map-asymptotically (asymptotically-Π H)
```
