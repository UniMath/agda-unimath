# Streams

```agda
{-# OPTIONS --guardedness #-}

module lists.streams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.equivalences

open import lists.lists
```

</details>

## Idea

**Streams** are, in a sense, the dual of lists. Whereas a [list](lists.lists.md)
is built inductively by constructors `nil cons`, a stream is _deconstructed_
coinductively by destructors `head tail`.

## Definitions

```agda
record stream {l : Level} (A : UU l) : UU l where
  coinductive
  field
    head : A
    tail : stream A

open stream public
```

### The coinduction principle of the type of streams

```agda
module _
  {l : Level} {A : UU l}
  where
```

### The counit and comultiplication laws of streams

```agda
counit-stream : {l : Level} {A : UU l} → stream A → A
counit-stream as = head as

comultiplication-stream : {l : Level} {A : UU l} → stream A → stream (stream A)
head (comultiplication-stream as) = as
tail (comultiplication-stream as) = comultiplication-stream as
```

## Properties

### Lists embed into streams

```agda
stream-list : {l : Level} {A : UU l} → list A → stream A
head (stream-list as) = {!   !}
tail (stream-list as) = {!   !}
```

### Characterizing the identity type of streams

```agda
record bisimulation {l : Level} {A : UU l} (xs ys : stream A) : UU l where
  coinductive
  field
    head-eq : head xs ＝ head ys
    tail-eq : bisimulation (tail xs) (tail ys)

open bisimulation public

refl-bisimulation : {l : Level} {A : UU l} (as : stream A) → bisimulation as as
head-eq (refl-bisimulation as) = refl
tail-eq (refl-bisimulation as) = refl-bisimulation (tail as)

eq-bisim : {l : Level} {A : UU l} (xs ys : stream A) → xs ＝ ys → bisimulation xs ys
eq-bisim xs xs refl = refl-bisimulation xs

bisim-eq : {l : Level} {A : UU l} (xs ys : stream A) → bisimulation xs ys → xs ＝ ys
bisim-eq {l} {A} xs ys p = {!   !}

is-torsorial-bisimulation : {l : Level} {A : UU l} (as : stream A) → is-torsorial (bisimulation as)
pr1 (is-torsorial-bisimulation as) = as , (refl-bisimulation as)
pr2 (is-torsorial-bisimulation as) (bs , bisim) = {!   !}
```

## External links

- [Coinduction](https://agda.readthedocs.io/en/latest/language/coinduction.html)
  at the Agda documentation

- [Streams](https://bartoszmilewski.com/2017/01/02/comonads/) at Bartosz
  Milewski's Programming Cafe
