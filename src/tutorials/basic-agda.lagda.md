# Tutorial on basic use of Agda

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module tutorials.basic-agda where
```

## Introduction

Welcome to the tutorial on basic use of Agda. Agda is a computer proof assistant. It can be used for formal mathematical reasoning, verification of software, and implementation and design of dependently typed programming languages. Here we will focus solely on the first use of Agda, as a proof assistant for mathematical reasoning.

## Further resources

There are many online resources that can help you learn more about Agda

* [The official Agda documentation](https://agda.readthedocs.io/en/v2.6.2.1/)
* [Martin Escardo's Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)
* [Thorsten Altenkirch's Computer Aided Formal Reasoning](http://www.cs.nott.ac.uk/~psztxa/g53cfr/)

## How to use Agda

To obtain Agda, follow the instructions from the [installation manual](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/installation.html) of the official Agda documentation. Agda can be used in either emacs or vscode. Here we will focus on Agda in emacs.

This tutorial is written in a literate Agda file. In our case, the file is named `basic-agda.lagda.md`, which means that we can write markdown code between the blocks of Agda code. A block of Agda code is opened with three back ticks followed by the letters `agda`, and it is closed with three back ticks. For example, the following block of Agda code introduces the type of natural numbers:

```agda
data ℕ : Set where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ
```

In emacs mode, the symbol ℕ for the natural numbers is obtained by typing `\bN`. Likewise, the arrow is obtained by typing `\to`. The emacs mode has support for many unicode characters. The [official documentation](https://agda.readthedocs.io/en/v2.6.2.1/tools/emacs-mode.html#unicode-input) explains how to use them.

### Defining basic operations on natural numbers

```agda
add-ℕ : ℕ → ℕ → ℕ
add-ℕ x zero-ℕ = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

another-add-ℕ : ℕ → ℕ → ℕ
another-add-ℕ zero-ℕ zero-ℕ = zero-ℕ
another-add-ℕ zero-ℕ (succ-ℕ y) = succ-ℕ y
another-add-ℕ (succ-ℕ x) zero-ℕ = succ-ℕ x
another-add-ℕ (succ-ℕ x) (succ-ℕ y) = succ-ℕ (succ-ℕ (another-add-ℕ x y))

mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ x zero-ℕ = zero-ℕ
mul-ℕ x (succ-ℕ y) = add-ℕ (mul-ℕ x y) x

-- idea:
-- add-ℕ x 0 := x
-- add-ℕ x (y+1) := (x+y)+1

-- idea:
-- mul-ℕ x zero-ℕ := zero-ℕ
-- mul-ℕ x (y+1) := (mul-ℕ x y) + x

-- use C-c C-c to case-split
-- use C-c C-e to ask agda about the assumption in the current context
-- use C-c C-Space to evaluate the answer

-- Laws are equations like x+y = y+x
```

### Equality in Agda

Equality in a proof assistant is expressed by the identity type

```agda
-- Id x y expresses that x and y are identical elements of type X
-- "The identity relation is the least reflexive relation on X"

data Id {X : Set} (x : X) : X → Set where
  refl : Id x x
```

### Equality is an equivalence relation

```agda
inv : {X : Set} {x y : X} → Id x y → Id y x
inv refl = refl

concat : {X : Set} {x y z : X} → Id x y → Id y z → Id x z
concat refl refl = refl
```

### Every function preserves equality

```agda
cgr : {X Y : Set} (f : X → Y) {x y : X} → Id x y → Id (f x) (f y)
cgr f refl = refl
```

### Addition on ℕ satisfies the usual laws

```agda
right-unit-law-add-ℕ : (x : ℕ) → Id (add-ℕ x zero-ℕ) x
right-unit-law-add-ℕ x = refl

left-unit-law-add-ℕ : (x : ℕ) → Id (add-ℕ zero-ℕ x) x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = cgr succ-ℕ (left-unit-law-add-ℕ x)

left-successor-law-add-ℕ :
  (x y : ℕ) → Id (add-ℕ (succ-ℕ x) y) (succ-ℕ (add-ℕ x y))
left-successor-law-add-ℕ x zero-ℕ = refl
left-successor-law-add-ℕ x (succ-ℕ y) = cgr succ-ℕ (left-successor-law-add-ℕ x y)

-- add-ℕ (succ-ℕ x) (succ-ℕ y)
-- := succ-ℕ (add-ℕ (succ-ℕ x) y)
-- = succ-ℕ (succ-ℕ (add-ℕ x y))
-- := succ-ℕ (add-ℕ x (succ-ℕ y))

commutative-add-ℕ : (x y : ℕ) → Id (add-ℕ x y) (add-ℕ y x)
commutative-add-ℕ x zero-ℕ = inv (left-unit-law-add-ℕ x)
commutative-add-ℕ x (succ-ℕ y) =
  concat
    ( cgr succ-ℕ (commutative-add-ℕ x y))
    ( inv (left-successor-law-add-ℕ y x))

another-add-is-add-ℕ : (x y : ℕ) → Id (another-add-ℕ x y) (add-ℕ x y)
another-add-is-add-ℕ zero-ℕ zero-ℕ = refl
another-add-is-add-ℕ zero-ℕ (succ-ℕ y) = inv (cgr succ-ℕ (left-unit-law-add-ℕ y))
another-add-is-add-ℕ (succ-ℕ x) zero-ℕ = refl
another-add-is-add-ℕ (succ-ℕ x) (succ-ℕ y) = {!!}

-- We will apply the left and the right unit laws
-- (x+0) = x = (0+x)

```

###
