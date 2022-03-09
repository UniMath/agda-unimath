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

mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ = {!!}

exp-ℕ : ℕ → ℕ → ℕ
exp-ℕ = {!!}
```

### Equality in Agda

Equality in a proof assistant is expressed by the identity type

```agda
data Id {X : Set} (x : X) : X → Set where
  refl : Id x x
```

### Equality is an equivalence relation

### Every function preserves equality

### Addition on ℕ satisfies the usual laws

###
