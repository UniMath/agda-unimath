# Univalent mathematics in Agda

[![CI](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml/badge.svg)](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml) [![Agda-Unimath website](https://github.com/UniMath/agda-unimath/actions/workflows/pages.yaml/badge.svg)](https://github.com/UniMath/agda-unimath/actions/workflows/pages.yaml)

The `agda-unimath` library is a new formalisation project for univalent mathematics in Agda. Our goal is to formalize an extensive curriculum of mathematics from the univalent point of view. Furthermore, we think libraries of formalized mathematics have the potential to be useful, and informative resources for mathematicians. Our library is designed to work towards this goal, and we welcome contributions to the library about any topic in mathematics.

The library is built in Agda 2.6.3. It can be compiled by running `make check` from the main folder of the repository.

## Links

1. [Agda-Unimath webpage](https://unimath.github.io/agda-unimath/)
2. [Discord](https://discord.gg/Zp2e8hYsuX)
3. [Twitch](https://www.twitch.tv/agdaunimath)

## Projects using the `agda-unimath` library

Here is a list of projects that use the `agda-unimath` library:

* https://git.app.uib.no/hott/hott-set-theory

If your project uses the `agda-unimath` library, let us know, so we can add your project to the list.

## Citing the `agda-unimath` library

```
@misc{Agda-UniMath,
  author =     {Egbert Rijke and Elisabeth Bonnevier and Jonathan Prieto-Cubides and others},
  title =     {Univalent mathematics in {Agda}},
  url =         {https://github.com/UniMath/agda-unimath/},
  howpublished = {\url{https://unimath.github.io/agda-unimath/}}
}
```

## Getting started

Before you can use the `agda-unimath` library, you should have Agda installed on your machine and an editor that is compatible with Agda. We recommend `Emacs` and `VSCode`.

### Installation guides and tutorials for Agda

 - Go to the [installation guide](https://agda.readthedocs.io/en/latest/getting-started/installation.html) on the Agda documentation page for instructions to install Agda.
 - Once you have Agda up and running, you can copy our library to your machine using `git clone git@github.com:UniMath/agda-unimath.git`.
 - If you're new to Agda, see the [list of tutorials](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html) to learn how to use Agda.

### Setting up emacs for literate Agda files

The `agda-unimath` library is written in literate markdown agda. This means that all the files in the formalization have the extension `.lagda.md` and they consist of markdown text and `agda` code blocks. For your emacs to handle these files correctly, you need to add the following line to your `.emacs` file:

```
(setq auto-mode-alist (cons '("\\.lagda.md$" . agda2-mode) auto-mode-alist))
```

### Setting up emacs for the notation of identity types

In the `agda-unimath` library, we use two notations for the identity type. The identity type is first introduced using Martin-Löf's original notation `Id`. Then we introduce as a secondary option the infix notation `_＝_`.

**Note**: The equals sign in the infix notation is not the standard equals sign on your keyboard, but it is the [full width equals sign](https://www.fileformat.info/info/unicode/char/ff1d/index.htm). Note that the full width equals sign is slightly wider, and it is highlighted in blue just like all the other defined constructions in Agda. In order to type the full width equals sign in Agda emacs mode, you need to add it to your Agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Click the `INS` button
- Type the regular equals sign `=` in the Key sequence field.
- Click the `INS` button
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the full width equals sign `＝`. While you're at it, you can also add the key sequence `yo` to obtain the Japanese symbol `ょ` for the Yoneda embedding.

### After the setup

With Agda installed and emacs correctly set up, you can start using the library. There is no need to install anything further. To compile the library, which is optional, run `make check` from the main folder of the repository. This generates the file `everything.lagda.md`, which imports all the files in the library and subsequently verifies them. You don't need to compile the entire library, however. You can simply open the file you're interested in and load it with Agda. This will verify the file and any prerequisites that are not already compiled.

## Joining the project and contributing

If you would like to contribute something to the `agda-unimath` library, the best way to start is to find us in our chat channels on the [Univalent Agda discord](https://discord.gg/Zp2e8hYsuX). We have a vibing community there, and you're more than welcome to join us just to hang out.

Once you've decided what you want to contribute, we recommend that you make your fork of the library. Within your fork, make a separate branch in which you will be making your contribution. Now you're ready to start your project! When you've completed your formalization you can proceed by making a pull request. Then we will review your contributions, and merge them when it is ready for the `agda-unimath` library.

## Statement of inclusion

There are many reasons to contribute something to a library of formalized mathematics. Some do it just for fun, some do it for their research, and some do it to learn something. Whatever your reason is, we welcome your contributions! To keep the experience of contributing something to our library enjoyable for everyone, we strive for an inclusive community of contributors. You can expect from us that we are kind and respectful in discussions, that we will be mindful of your pronouns and use [inclusive language](https://www.apa.org/about/apa/equity-diversity-inclusion/language-guidelines), and that we value your input regardless of your level of experience or status in the community. We're committed to providing a safe and welcoming environment to people of any gender identity, sexual orientation, race, colour, age, ability, ethnicity, background, or fluency in English -- here on GitHub, in online communication channels, and in person. Homotopy type theory is difficult enough without all the barriers that many of us have to face, so we hope to bring some of those down a bit.

:rainbow: Happy contributing!

Elisabeth Bonnevier  
Jonathan Prieto-Cubides  
Egbert Rijke

## Design of the library

### Postulates in the library

The `agda-unimath` library is a library of formalized mathematics in vanilla Agda. Throughout our library, we assume the `--without-K` and `--exact-split` flags of Agda. Furthermore, we assume some postulates.

1. We make full use of Agda's `data` types for introducing inductive types.
2. We make full use of Agda's universe levels, including `ω`. However, it should be noted that most of the type constructors only define types of universe levels below `ω`, so a lot of the theory developed in this library does not apply to universe level `ω` and beyond.
3. The **function extensionality axiom** is postulated in [`foundation-core.function-extensionality`](https://unimath.github.io/agda-unimath/foundation-core.function-extensionality.html).
4. The **univalence axiom** is postulated in [`foundation-core.univalence`](https://unimath.github.io/agda-unimath/foundation-core.univalence.html).
5. The type theoretic **replacement axiom** is postulated in [`foundation.replacement`](https://unimath.github.io/agda-unimath/foundation.replacement.html)
6. The **truncation operations** are postulated in [`foundation.truncations`](https://unimath.github.io/agda-unimath/foundation.truncations.html)
7. The **interval** is postulated in [`synthetic-homotopy-theory.interval-type`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.interval-type.html)
8. The **circle** is postulated in [`synthetic-homotopy-theory.circle`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.circle.html)
9. **Pushouts** are postulated in [`synthetic-homotopy-theory.pushouts`](https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.pushouts.html)

Note that there is some redundancy in the postulates we assume. For example, the [univalence axiom implies function extensionality](https://unimath.github.io/agda-unimath/foundation.univalence-implies-function-extensionality.html), but we still assume function extensionality separately. Furthermore, The interval type is contractible, so there is no need at all to postulate it. The circle can be constructed as the type of `ℤ`-torsors, and the replacement axiom can be used to prove there is a circle in `UU lzero`. Finally, the replacement axiom can be proven by the join construction, which only uses pushouts.

We also note that the higher inductive types in the `agda-unimath` library only have computation rules up to identification.

With these postulates, the `agda-unimath` library is a library for constructive univalent mathematics. Mathematics for which the law of excluded middle or the axiom of choice is necessary is not yet developed in `agda-unimath`. However, we are also open to any development of classical mathematics within `agda-unimath`, and we do also welcome contributions in that direction.

### Structure of the library

1. The source code of the formalisation can be found in the folder `src`.
2. The library is organized by mathematical subject, with one folder per mathematical subject. For each folder, there is also an Agda file of the same name, which lists the files in that folder by importing them publicly.
3. The `agda-unimath` library has the goal to be an informative resource of formalised mathematics. We therefore formalise in literate agda, using markdown. We think of the files in the formalisation as pages of a wiki on mathematics.
4. The files focus sharply on one topic. Typically, a file begins by introducing one new concept, possibly in several equivalent ways, and developing the most basic properties thereof. Alternatively, a file could have the goal to prove an important theorem, and derive immediate corollaries thereof.

### The design philosophy of `agda-unimath`

When a human is looking for something in a library of formalized mathematics, they likely have a clear idea of what concept they are looking for. It would be unlikely, however, that they know exactly what other concepts the concept they are looking for depends on. If the concept they're looking for is an instance of something more general, we also cannot count on it that they know about that this is the case. Certainly, we wouldn't require humans to know anything at all about _how_ their concept has been formalized in order to find it in `agda-unimath`. In fact, Humans might not yet know very much about the concept they're looking for except the name, and they might have come to find more information about it. The best case scenario for someone like that is that they can readily find their concept being listed in a hyperlinked index, like the index in the back of a book, so that they can find it there, click on it, and find what they were looking for.

Concepts are made prominent in the `agda-unimath` library because humans know how to look for them. An index of the concepts formalized in `agda-unimath` is formed by the list of files in the library, and the indexing terms are the file names. Since we want to help humans to easily find the topics they're interested in, all the files in our library are narrowly focused on one concept, on one named theorem or on one specific topic. The file names describe that concept, theorem, or topic in a concise and natural manner.

This choice of organization of the library implies that we can organize our files much like pages on a wiki. The title of the file is the topic at hand, in an informal section we can describe in words what the main idea is; then we give the main definition, the basic infrastructure around it, and we derive properties or consequences that hold in the same generality as the main definition of the file.

For example, the file about sets defines first what a set is, and then goes on to show that sets are closed under equivalences, dependent pair types, dependent product types, and so on. But it doesn't show that the type of natural numbers is a set because users would more likely expect such a fact to be presented on the page about natural numbers.

Now we can do a thought experiment. Suppose we have an unorganized library of mathematics, and we organize everything by topic as described above. Mathematics is already a well-organised subject, so for most of the library this is our preferred way to organise it. But at the bottom of the library we will find a cluster of interdependent files, and Agda will give errors because of those cyclic dependencies. This is because our desire to organise the library by topic doesn't take the bootstrapping process of getting things off the ground at the foundational level of the library. 

To resolve those cyclic dependencies, we created two folders for the foundation of the `agda-unimath` library: the `foundation-core` folder containing the basic setup, and the `foundation` folder, containing everything that belongs to the foundation of the library. The `foundation-core` folder contains files that are paired with files of the same name in the `foundation` folder. The corresponding file in the `foundation` folder imports this file from the `foundation-core` folder publicly. Users who are working in areas outside of the foundation can just import files directly from `foundation`, and they don't have to worry that some files might be split in two.

Outside of the `foundation` folder of the library, we stick to the "one-concept-per-file" design principle of our library. If you find, however, that something you were looking for was not in the place you expected it to be (this happens!) please let us know and we will consider it for improvements.

### Style conventions for files

1. File names are descriptive of the concept it introduces, or the main theorem it proves. The file names could be considered indexing terms, with the list of files functioning much like the index in the back of a book. Usually, file names consist of a noun or a noun phrase. File names should be natural, sufficiently precise, concise, and consistent with those of related files. 
2. File names are entirely in lowercase, with words separated by hyphens. Words in file names should not be abbreviated unless the abbreviated term is a widely accepted mathematical term, e.g., `poset`.
3. Files that are part of the formalisation should be in literate agda using markdown. They should have the file extension `.lagda.md`.
4. Every file should begin with a header in the following format
```md
---
title: [The title of the file]
---
```
5. Immediately after the header, there should be a block of Agda code that loads the options, declares the present module, and performs all the imports. In particular, there should be no further imports later on in the file.
6. The rest of the files is divided into sections, subsections and possibly subsubsections. Each section should have a markdown header of level `##`, and the title of each header should be generic, such as `Idea`, `Definition`, `Example`, `Properties`, and so on. 
7. The subsections should have a markdown header of level `###` and they should concisely describe the content of the block of code that follows.

Ideally, the first section of a file explains the idea, then proceeds to give the main definition that is the focus of the current file, then proceeds possibly with examples and by deriving basic properties of the defined concept. We suggest adopt the following template:

```md
---
title: [The title of this file]
---

Contributors : [The list of contributors]

[ options
  module declaration
  imports]

## Idea

( Informal description of the idea)

## Definitions

### Definition 1

( Contributor of this definition (optional))

[ formalization of the definition and immediately related structure]

## Examples

### X is an example

( Contributor of this definition (optional)
  Informal explanation)

[ formalization that X is an example]

### Y is an example

( Contributor of this example (optional)
  Informal explanation)

[ formalization that Y is an example]

## Properties

### Concise descrition of property 1

( Contributor of this property (optional)
  Informal explanation)

[ formalization of property 1]

### Concise description of property 2

( Contributor of this property (optional)
  Informal explanation)

[ formalization of property 2]

## Related concepts

## References
```

### KaTeX support for the website

The website of the `agda-unimath` library has support for KaTeX. See the [list of supported functions](https://katex.org/docs/supported.html) in Katex.

### Library conventions

* This style guide is here to improve the readability of the code. If an item
  in this guide causes suboptimal readability of the code if applied, please
  notify us and we will try to improve this guide, and possibly our code.
* The library uses a standard line length of 80 characters.
* All module headers and standard term definitions should have a single empty line before and after them.
* The library uses Lisp-style parentheses, and indent arguments of functions if they are on their own line.
* The library is universe polymorphic. Whenever a type or type family is assumed, it is assigned its own universe level.

#### Names

The naming convention in this library is such that the name of a construction closely matches the type of the construction. For example, the proof that the successor function on the integers is an equivalence has type `is-equiv succ-ℤ`. The name of the proof that the successor function on the integers is an equivalence is therefore `is-equiv-succ-ℤ`. Notice that most names are fully lowercase, and words are separated by hyphens. 

Names may also refer to types of the hypotheses used in the construction. Since the first objective of a name is to describe the type of the constructed term, the description of the hypotheses comes after the description of the conclusion in a name. For example, the term `is-equiv-is-contr-map` is a function of type `is-contr-map f → is-equiv f`, where `f` is a function already assumed. This convention has the advantage that if we have `H : is-contr-map f`, then the term `is-equiv-is-contr-map H` contains the description `is-contr-map` closest to the variable `H` of which it is a description.

Our naming conventions are not to ensure the shortest possible names, and neither to ensure the least amount of typing by the implementers of the library, but to display as accurately as possible what concepts are applied, and hence improve the readability.

* We do not use namespace overloading. Unique names should be given to each construction.
* Names should describe in words the concept of its construction.
* As a rule of thumb, names should be entirely lowercase, with words separated by hyphens.
* Names describe the object that is constructed first. For some theorems, the later part of a name contains descriptions of the hypotheses.
* Names never refer to variables.
* Important concepts can be capitalized. Usually, capitalized concepts form categories. Examples include `UU`, `Prop`, `Set`, `Semigroup`, `Monoid`, `Group`, `Preorder`, `Poset`, `Precat`, `Cat`, `Graph`, `Undirected-Graph`.
* The capitalized part of a name only appears at the end of the name.
* Unicode symbols are used sparingly, and only following established mathematical practice.
* Abbreviations are used sparingly, as they also impair the readability of the code.
* If a symbol is not available, the concept is described in words or abbreviated words. For example, the equality symbol = is not available to the user to assert an equality. Hence, we write Id x y to assert equality, referring to the identity type, and we do not use a new symbol.
* The readability of the code has a high priority. Therefore we try to avoid subtly different variations of the same symbol.

- The naming scheme for the underlying type of a structured type is `type-"Name of the structured type"`. For example, the underlying type of the set `hom-C X Y` of morphisms from `X` to `Y` in a category `C` is `type-hom-C X Y`.
- The naming scheme for the underlying map of a structured map is `map-"Name of the structured map"`. For example, the underlying map of an equivalence `e` is `map-e`.
- Equivalences that are thought of as computing a certain type are called `compute-"Name of what they compute"`. Typically, we want this equivalence to go in the direction from the computed value to the type being computed. This is for practical purposes: the computed value of a type is often simpler and we want to use it to construct elements in the type that is being computed. This use case suggests the direction of the equivalence.

#### Indentation

* The contents of a top-level module should have zero indentation.
* Every subsequent nested scope should then be indented by an additional two spaces.
* If the variables of a module do not fit on a line, start the variable declarations on a new line, with an indentation of two spaces.
* If the name of a construction does not fit on a single line with its type declaration, then we start the type declaration on a new line, with an indentation of two additional spaces. If the type specification of a construction then still does not fit on a single line of 80 characters, we start new lines in the type declaration using the same indentation level.
* Function arrows at line breaks should always go at the end of the line rather than the beginning of the next line.

#### Modules

* Using anonymous modules is encouraged to group constructions by topic, introducing the common arguments of those constructions as parameters.
* As a rule of thumb, there should only be one named module per file. The other modules in the file should be anonymous.
* There should always be a single blank line after a module declaration.
* The variables of a module should be declared on a new line, with a 2-space indentation level. If the variables don't fit on a single line, they can be declared over multiple lines, grouping the variables together logically.
* The `where` keyword is positioned on a new line after the variable declarations, with a 2-space indentation level.
  
```agda
module _
  {l : Level} (G : Group l)
  where
```
  
#### Layout of `where` blocks

* `where` blocks are preferred rather than the `let` construction.
* `where` blocks should be indented by two spaces and their contents should be aligned with the `where`.
* The `where` keyword should be placed on the line below the main proof, indented by two spaces.
* Types should be provided for each of the terms, and all terms should be on lines after the `where`, e.g.
  ```agda
  statement : Statement
  statement = proof
    where
    proof : Proof
    proof = some-very-long-proof
  ```

#### Functions

* We do not align the arguments or the equality symbol in a function definition.
* If an argument is unused in a function definition, an underscore may be used.
* If a clause of a construction does not fit on the same line as the name and variable declaration, we start the definition on a new line with two spaces of additional indentation

#### Types

* Function arguments should be implicit if they can "almost always" be inferred within proofs. It is often harder for Agda to infer an argument in a type declaration, but we prioritize usage in proofs in our decision to make an argument implicit.
* If there are lots of implicit arguments that are common to a collection of proofs they should be extracted by using an anonymous module.
* The library doesn't use variables at the moment. All variables are declared either as parameters of an anonymous module or in the type declaration of a construction.

#### Coding practices we avoid

* Unicode characters in names are allowed but use them sparingly. If it is overdone, it will be more difficult to read.
* Names of constructions should never refer to variable names.
* Don't use deeply indented code if a two-space indentation level suffices. Deeply indented code will be rendered unreadable on smaller screens.
* Don't use long lines of code, for the same reason.
* `where` blocks are allowed, but keep them short. Large `where` blocks tend to result in non-reusable and non-refactorable code, and in some instances they slow down Agda's verification process.
* We don't make much use of record types in the `agda-unimath` library. This is because they make it a hassle to characterize their identity type, which is often the first thing we do with a new type. If characterizing the identity type is less relevant, then of course it is convenient to use record types.
* The use of the projection functions `pr1` and `pr2`, and especially their compositions, should be very limited. If a type of the form `Σ A B` is given a name, then it is also worth giving the projections a name. This makes the code more readable, and furthermore if we now jump to the definition of the named projection we will see an informative answer.
* We don't name constructions after infix notation of any operation that occurs in it. Infix notation is always secondary, and in later names that refer to a construction that has infix notation, we refer to the primary prefix notation. For example, the name for the commutativity of cartesian products is `commutative-prod` and not `commutative-×`.
